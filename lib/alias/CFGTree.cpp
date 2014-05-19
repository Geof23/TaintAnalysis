#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "TaintAnalysis.h"
#include <iostream>
#include <fstream>

namespace runtime {
  extern cl::opt<bool> Verbose;
}

using namespace taint;
using namespace runtime;

/*static void extractInstFromSourceCode(MDNode *N) {
  DILocation Loc(N);               // DILocation is in DebugInfo.h
  unsigned Line = Loc.getLineNumber();
  StringRef File = Loc.getFilename();
  StringRef Dir = Loc.getDirectory();
  std::cout << "Instruction Line: " << Line << ", In File: "
            << File.str() << ", With Dir Path: " << Dir.str()
            << std::endl;

  std::string filePath = Dir.str() + "/" + File.str();
  std::ifstream src(filePath.data(), std::ifstream::in);
  if (src.is_open()) {
    unsigned num = 0;
    std::string cLine;
    do {
      getline(src, cLine);
      num++;
    } while (num != Line);

    std::cout << "[File: " << filePath << ", Line: " << Line
              << ", Inst: " << cLine << "]" << std::endl;
  } else {
    std::cout << "Can not open file!" << std::endl;
  }
}

static void dumpBrInstForTesting(CFGNode *node) {
  Instruction *inst = node->inst;
  if (MDNode *N = inst->getMetadata("dbg")) {  
    // Here I is an LLVM instruction
    extractInstFromSourceCode(N);
    inst->dump();
  } 
}*/

CFGTree::CFGTree() {
  root = current = flowCurrent = iterateCFGNode = NULL;
  nodeNum = 0;
  syncthreadEncounter = false;
}

CFGTree::~CFGTree() {
  destroyCFGTree(root);
}

void CFGTree::destroyCFGTree(CFGNode *node) {
  if (node != NULL) {
    std::vector<CFGNode*> &treeNodes = node->cfgNodes;              

    for (unsigned i = 0; i < treeNodes.size(); i++) {                              
      destroyCFGTree(treeNodes[i]);
      treeNodes[i] = NULL;
    } 
    // we should also remove this node 
    destroyCFGTree(node->successor); 
    node->successor = NULL;

    node->parent = NULL;
    delete node;
  } 
}

CFGNode* CFGTree::getRootNode() {
  return root;
}

CFGNode* CFGTree::getCurrentNode() {
  return current;
}

CFGNode* CFGTree::getFlowCurrentNode() {
  return flowCurrent;
}

bool CFGTree::inIteration() {
  return iterateCFGNode != NULL;
}

void CFGTree::insertNodeIntoCFGTree(CFGNode *node) {
  if (root == NULL) {
    root = current = flowCurrent = node;
    nodeNum = 1;
    return; 
  }

  if (current->allFinish) {
    CFGNode *tmp = current;
    while (tmp->successor != NULL)
      tmp = tmp->successor;
    assert(tmp->allFinish && "check in insertNodeIntoCFGTree, not both finished");
    tmp->successor = node;
    node->parent = tmp;
  } else {
    std::vector<CFGNode*> &nodes = current->cfgNodes;
    if (nodes[current->which]) {
      CFGNode *tmp = nodes[current->which];
      while (tmp->successor != NULL) 
        tmp = tmp->successor;
      assert(tmp->allFinish && "check in insertNodeIntoCFGTree, not both finished");
      tmp->successor = node; 
      node->parent = tmp;
    } else {
      nodes[current->which] = node;
      node->parent = current;
    }
  }
  // set the current as the newly inserted node
  current = node;
  if (syncthreadEncounter) {
    flowCurrent = node;
    syncthreadEncounter = false;
  }
  nodeNum++;   
}

static bool isTwoInstIdentical(Instruction *inst1, 
                               Instruction *inst2) {
  std::string func1Name = inst1->getParent()->getParent()->getName().str();
  std::string func2Name = inst2->getParent()->getParent()->getName().str();

  BasicBlock *bb1 = inst1->getParent();
  BasicBlock *bb2 = inst2->getParent();

  return func1Name.compare(func2Name) == 0
           && bb1 == bb2
             && inst1->isIdenticalTo(inst2);
}

bool CFGTree::resetCurrentNodeInCFGTree(CFGNode *node, 
                                        Instruction *inst) {
  bool currentSet = false;

  if (node) {
    if (isTwoInstIdentical(node->inst, inst)) {
      current = node;
      current->which = 0;
      current->allFinish = false;
      currentSet = true;
    }

    if (!currentSet) { 
      for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
        currentSet = resetCurrentNodeInCFGTree(node->cfgNodes[i], 
                                               inst);
        if (currentSet) break;
      }
      if (!currentSet)
        currentSet = resetCurrentNodeInCFGTree(node->successor, 
                                               inst);
    }
  }
   
  return currentSet;
} 

void CFGTree::exploreCFGUnderIteration(Instruction *inst) {
  bool reset = resetCurrentNodeInCFGTree(root, inst);
  assert(reset && "current is not set correctly!"); 
}

bool CFGTree::isCFGTreeFullyExplored() {
  if (!iterateCFGNode) {
    if (current) {
      return current->allFinish;
    } else 
      return true; 
  } else 
    return false;
}

static bool checkTwoTaintArgSetSame(std::vector<TaintArgInfo> &set1, 
                                    std::vector<TaintArgInfo> &set2) {
  assert(set1.size() == set2.size() && "The size of set1 and set2 differs");

  for (unsigned i = 0; i < set1.size(); i++) {
    bool instListSame = set1[i].taintInstList.size() 
                          == set2[i].taintInstList.size();
    bool valueSetSame = set1[i].taintValueSet.size() 
                          == set2[i].taintValueSet.size();
    bool same = instListSame && valueSetSame;

    if (!same) return false;
  }

  return true;
} 

void ExecutorUtil::checkLoadInst(Instruction *inst, 
                                 std::vector<GlobalSharedTaint> &glSet, 
                                 std::vector<GlobalSharedTaint> &sharedSet, 
                                 AliasAnalysis &AA, 
                                 RelFlowSet &flowSet) {
  bool relToShared = false;
  LoadInst *load = dyn_cast<LoadInst>(inst); 
  Value *pointer = load->getPointerOperand();
 
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(pointer, 
                                            sharedSet[i].instSet, 
                                            sharedSet[i].valueSet)) {
      // Related to shared
      if (Verbose > 0) {
        std::cout << "shared load inst: " << std::endl;
        inst->dump();
      }
      flowSet.sharedReadVec.insert(sharedSet[i].gv);
      relToShared = true;
      break;
    }
  }

  if (!relToShared) {
    for (unsigned i = 0; i < glSet.size(); i++) {
      if (ExecutorUtil::findValueFromTaintSet(pointer,
                                              glSet[i].instSet, 
                                              glSet[i].valueSet)) {
        // Related to global 
        flowSet.globalReadVec.insert(glSet[i].gv);
        if (Verbose > 0) {
          std::cout << "global load inst: " << std::endl;
          inst->dump();
        }
        break; 
      }
    }
  }
} 

void ExecutorUtil::checkStoreInst(Instruction *inst, 
                                  std::vector<GlobalSharedTaint> &glSet, 
                                  std::vector<GlobalSharedTaint> &sharedSet, 
                                  AliasAnalysis &AA, 
                                  RelFlowSet &flowSet) {
  bool relToShared = false;
  StoreInst *store = dyn_cast<StoreInst>(inst); 
  Value *pointer = store->getPointerOperand(); 
 
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(pointer, 
                                            sharedSet[i].instSet, 
                                            sharedSet[i].valueSet)) {
      // Related to shared
      if (Verbose > 0) {
        std::cout << "shared store inst: " << std::endl;
        inst->dump();
      }
      flowSet.sharedWriteVec.insert(sharedSet[i].gv);
      relToShared = true;
      break;
    }
  }

  if (!relToShared) {
    for (unsigned i = 0; i < glSet.size(); i++) {
      if (ExecutorUtil::findValueFromTaintSet(pointer,
                                              glSet[i].instSet, 
                                              glSet[i].valueSet)) {
        // Related to global 
        if (Verbose > 0) {
          std::cout << "global store inst: " << std::endl;
          inst->dump();
        }
        flowSet.globalWriteVec.insert(glSet[i].gv);
        break; 
      }
    }
  }
}

void ExecutorUtil::checkAtomicInst(Instruction *inst, 
                                   std::vector<GlobalSharedTaint> &glSet, 
                                   std::vector<GlobalSharedTaint> &sharedSet, 
                                   AliasAnalysis &AA, 
                                   RelFlowSet &flowSet) {
  bool relToShared = false;
  Value *pointer = inst->getOperand(0);
  
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(pointer, 
                                            sharedSet[i].instSet, 
                                            sharedSet[i].valueSet)) {
      // Related to shared
      if (Verbose > 0) {
        std::cout << "shared store inst: " << std::endl;
        inst->dump();
      }
      flowSet.sharedReadVec.insert(sharedSet[i].gv);
      flowSet.sharedWriteVec.insert(sharedSet[i].gv);
      relToShared = true;
      break;
    }
  }

  if (!relToShared) {
    for (unsigned i = 0; i < glSet.size(); i++) {
      if (ExecutorUtil::findValueFromTaintSet(pointer,
                                              glSet[i].instSet, 
                                              glSet[i].valueSet)) {
        // Related to global 
        if (Verbose > 0) {
          std::cout << "global store inst: " << std::endl;
          inst->dump();
        }
        flowSet.globalReadVec.insert(glSet[i].gv);
        flowSet.globalWriteVec.insert(glSet[i].gv);
        break; 
      }
    }
  }
} 

void CFGTree::insertCurInst(Instruction *inst, 
                            std::vector<TaintArgInfo> &taintArgSet,
                            AliasAnalysis &AA,
                            std::vector<GlobalSharedTaint> &glSet,
                            std::vector<GlobalSharedTaint> &sharedSet) {
  if (!current->allFinish) {
    unsigned which = current->which;
    CFGInstSet &cfgInstSet = current->cfgInstSet[which];    
    cfgInstSet.instSet.insert(inst);

    /*
    std::cout << "insertCurInst cfgInstSet which: " << which << " explored : " 
              << cfgInstSet.explore << ", the inst Set: " 
              << std::endl;
    for (std::set<Instruction*>::iterator si = cfgInstSet.instSet.begin();
         si != cfgInstSet.instSet.end(); si++) {
      (*si)->dump();
    }
    */

    // To determine if the pointer operand in the 'Load' instruction
    // conflicts with shared/global variable 
    if (inst->getOpcode() == Instruction::Load) {
      if (Verbose > 0) {
        std::cout << "load inst: " << std::endl;
        inst->dump();
      }
      ExecutorUtil::checkLoadInst(inst, glSet, sharedSet, 
                                  AA, current->cfgFlowSet[which]);
    }

    // To determine if the pointer operand in the 'Store' instruction
    // conflicts with shared/global variable 
    if (inst->getOpcode() == Instruction::Store) {
      if (Verbose > 0) {
        std::cout << "store inst: " << std::endl;
        inst->dump();
      }
      ExecutorUtil::checkStoreInst(inst, glSet, sharedSet, 
                                   AA, current->cfgFlowSet[which]);
    }

    std::string instName = inst->getName().str();
    if (instName.find("Atomic") != std::string::npos) {
      ExecutorUtil::checkAtomicInst(inst, glSet, sharedSet, 
                                    AA, current->cfgFlowSet[which]);
    }
  } else {
    std::set<Instruction*> &instSet = current->succInstSet.instSet;
    instSet.insert(inst);

    if (inst->getOpcode() == Instruction::Load)
      ExecutorUtil::checkLoadInst(inst, glSet, sharedSet, 
                                  AA, current->succFlowSet);

    if (inst->getOpcode() == Instruction::Store)
      ExecutorUtil::checkStoreInst(inst, glSet, sharedSet, 
                                   AA, current->succFlowSet);
  }
}

void CFGTree::dumpNodeInstForDFSChecking(CFGNode *node, 
                                         unsigned i) {
  std::cout << "set here in startDFSChecking, i: " 
            << i << std::endl;
  node->inst->dump();
}

// detect if the potential shared/global race 
// exist within the current BI or across different BIs 
CombineResult CFGTree::startDFSCheckingForCurrentBI(CFGNode *node) {
  CombineResult result;

  if (node != NULL) {
    for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
      if (node->cfgInstSet[i].explore == false) { 
        CombineResult res = startDFSCheckingForCurrentBI(node->cfgNodes[i]); 
        if (res.explore) {
          result.explore = true;
          node->cfgInstSet[i].explore = true;

          // set global
          if (node->cfgInstSet[i].global) {
            result.global = true; 
          } else { 
            if (res.global)
              node->cfgInstSet[i].global = true;
          }
          // set shared 
          if (node->cfgInstSet[i].shared) {
            result.shared = true; 
          } else { 
            if (res.shared) {
              node->cfgInstSet[i].shared = true;
            }
          }
        }
      } else { 
        CombineResult res = startDFSCheckingForCurrentBI(node->cfgNodes[i]);
        result.explore = true;

        // set global
        if (node->cfgInstSet[i].global)
          result.global = true;
        else {
          if (res.global)
            node->cfgInstSet[i].global = true;
        }
        // set shared 
        if (node->cfgInstSet[i].shared) {
          result.shared = true;
        } else {
          if (res.shared) {
            node->cfgInstSet[i].shared = true;
          }
        }
      }
    }
    // explore node's successor
    //startDFSCheckingForCurrentBI(node->successor); 
  }

  return result; 
}

void CFGTree::setSyncthreadEncounter() {
  syncthreadEncounter = true;
  flowCurrent = NULL;
}

bool CFGTree::foundSameBrInstFromCFGTree(Instruction *inst, 
                                         CFGNode *node) {
  bool found = false;

  if (node) { 
    if (isTwoInstIdentical(inst, node->inst))
      found = true;
      
    if (!found) {
      for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
        found = foundSameBrInstFromCFGTree(inst, 
                                           node->cfgNodes[i]);  
        if (found) break;
      }
      if (!found)
        found = foundSameBrInstFromCFGTree(inst, 
                                           node->successor); 
    }
  }

  return found;
}

bool CFGTree::identifySuccessorRelation(BasicBlock *predBB, 
                                        BasicBlock *succBB) {
  bool identify = false;
  BasicBlock *bb = predBB;
 
  while (true) {
    Instruction *inst = &(bb->back());
    if (inst->getOpcode() == Instruction::Br) {
      BranchInst *bi = dyn_cast<BranchInst>(inst);
      if (bi->isUnconditional()) {
        bb = bi->getSuccessor(0); 
        if (bb == succBB) {
          identify = true;
          break;
        }
      } else {
        identify = foundSameBrInstFromCFGTree(inst, root); 
        break;
      }
    } else {
      if (inst->getOpcode() == Instruction::Ret)
        break;
      else 
        assert(false && "Unsupported instruction!"); 
    }
  }
  
  return identify; 
}

static bool brTransferToLoop(Instruction *inst) {
  BranchInst *bi = dyn_cast<BranchInst>(inst);
   
  for (unsigned i = 0; i < bi->getNumSuccessors(); i++) {
    BasicBlock *bb = bi->getSuccessor(i);
    std::string bbName = bb->getName().str();

    if (bbName.find("while") != std::string::npos
        || bbName.find("for") != std::string::npos
          || bbName.find("do") != std::string::npos)
      return true; 
  }
  return false;
}

bool CFGTree::enterIteration(Instruction *inst, 
                             std::set<BasicBlock*> &exploredBBSet) {
  if (!iterateCFGNode 
       && brTransferToLoop(inst)) {
    BasicBlock *instBB = inst->getParent();
    return exploredBBSet.find(instBB) != exploredBBSet.end();
  }
  return false;
}

void CFGTree::updateCurrentNode(Instruction *inst, 
                                bool &transfer) {
  CFGNode *tmp = current;
  BasicBlock *bb = inst->getParent();

  while (tmp != NULL) {
    if (tmp->allFinish) {
      if (tmp->parent)
        tmp = tmp->parent;
      else 
        break;
    } else {
      if (tmp->postDom == bb) {
        if (Verbose > 0) {
          std::cout << "in CFG, postDom found, the branch inst: " << std::endl;
          tmp->inst->dump();
        }
        tmp->which++;
        std::vector<CFGNode*> &nodeSet = tmp->cfgNodes;
        if (tmp->which == nodeSet.size()) {
          tmp->allFinish = true;
          if (tmp->parent)
            tmp = tmp->parent; 
          else 
            break;
        } else {
          transfer = true;
          break;
        } 
      } else break; 
    }
  }
  if (Verbose > 0) {
    std::cout << "Move to node's which: " << tmp->which << std::endl;
    tmp->inst->dump(); 
  }
  current = tmp;
}

void CFGTree::setCFGNodeWithCauseIteration() {
  current->allFinish = true;
  current->which = current->cfgNodes.size();  
}

void CFGTree::updateCurrentNodeAfterIteration() {
  CFGNode *tmp = current;

  while (tmp != NULL) {
    if (tmp->allFinish) {
      if (tmp->parent)
        tmp = tmp->parent;
      else 
        break;
    } else break;
  }
  current = tmp;

  if (Verbose > 0)
    std::cout << "Jump out from the loop!" << std::endl;
}

void CFGTree::updateTaintInfoSet(std::vector<TaintArgInfo> &taintArgSet) {
  if (!iterateCFGNode) {
    taintInfoSet = taintArgSet;
    iterateCFGNode = current;
  }
}

bool CFGTree::updateCFGTree(Instruction *inst, 
                            std::vector<TaintArgInfo> &taintArgSet, 
                            std::set<BasicBlock*> &exploredBBSet, 
                            bool blockChange, bool &finishIteration) {
  bool transfer = false;

  if (iterateCFGNode) {
    if (isTwoInstIdentical(inst, iterateCFGNode->inst)) {
      current = iterateCFGNode;

      if (checkTwoTaintArgSetSame(taintInfoSet, taintArgSet)) {
        if (Verbose > 0) {
          std::cout << "set the iteration br: " 
                    << std::endl;
          current->inst->dump();
        }

        iterateCFGNode->causeIteration = true;
        iterateCFGNode->outOfIteration = current->which;
        current->which++;
        if (current->which == current->cfgNodes.size()) {
          current->allFinish = true;
          updateCurrentNodeAfterIteration();
          finishIteration = true;
        } 
        transfer = true;
           
        iterateCFGNode = NULL;
      } else {
        taintInfoSet = taintArgSet;
      }
    } else {
      //std::cout << "current inst: " << std::endl;
      //current->inst->dump();
      if (inst->getOpcode() == Instruction::Br
           && current->causeIteration) {
        //std::cout << "outOfIteration == 1" << std::endl;
        current->which = current->cfgNodes.size();
        current->allFinish = true;
        updateCurrentNodeAfterIteration(); 
        finishIteration = true;
        transfer = true;
      }
    }
  }
  updateCurrentNode(inst, transfer); 

  return transfer;
}
