#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "TaintAnalysis.h"

namespace runtime {
  extern cl::opt<bool> Verbose;
}

using namespace taint;
using namespace runtime;

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
      flowSet.sharedReadVec.push_back(RelValue(inst, sharedSet[i].gv));
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
        flowSet.globalReadVec.push_back(RelValue(inst, glSet[i].gv));
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
      flowSet.sharedWriteVec.push_back(RelValue(inst, sharedSet[i].gv));
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
        flowSet.globalWriteVec.push_back(RelValue(inst, glSet[i].gv));
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
      flowSet.sharedReadVec.push_back(RelValue(inst, sharedSet[i].gv));
      flowSet.sharedWriteVec.push_back(RelValue(inst, sharedSet[i].gv));
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
        flowSet.globalReadVec.push_back(RelValue(inst, glSet[i].gv));
        flowSet.globalWriteVec.push_back(RelValue(inst, glSet[i].gv));
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

    /*std::cout << "insertCurInst cfgInstSet which: " << which << " explored : " 
              << cfgInstSet.explore << ", the inst Set: " 
              << std::endl;
    for (std::set<Instruction*>::iterator si = cfgInstSet.instSet.begin();
         si != cfgInstSet.instSet.end(); si++) {
      (*si)->dump();
    }*/

    // To determine if the pointer operand in the 'Load' instruction
    // conflicts with shared/global variable 
    if (inst->getOpcode() == Instruction::Load)
      ExecutorUtil::checkLoadInst(inst, glSet, sharedSet, 
                                  AA, current->cfgFlowSet[which]);

    // To determine if the pointer operand in the 'Store' instruction
    // conflicts with shared/global variable 
    if (inst->getOpcode() == Instruction::Store)
      ExecutorUtil::checkStoreInst(inst, glSet, sharedSet, 
                                   AA, current->cfgFlowSet[which]);

    std::string instName = inst->getName().str();
    if (instName.find("Atomic") != std::string::npos) {
      ExecutorUtil::checkAtomicInst(inst, glSet, sharedSet, 
                                    AA, current->cfgFlowSet[which]);
    }
  } else {
    std::set<Instruction*> &instSet = current->succInstSet;
    instSet.insert(inst);

    if (inst->getOpcode() == Instruction::Load)
      ExecutorUtil::checkLoadInst(inst, glSet, sharedSet, 
                                  AA, current->succFlowSet);

    if (inst->getOpcode() == Instruction::Store)
      ExecutorUtil::checkStoreInst(inst, glSet, sharedSet, 
                                   AA, current->succFlowSet);
  }
}

static bool checkGlobalFlowSet(RelFlowSet &flowSet1, RelFlowSet &flowSet2) {
  bool check = false;

  if (!flowSet1.globalReadVec.empty()
       && !flowSet2.globalWriteVec.empty()) {
    for (unsigned i = 0; i < flowSet1.globalReadVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.globalWriteVec.size(); j++) {
        if (flowSet1.globalReadVec[i].relVal 
             == flowSet2.globalWriteVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  if (!flowSet1.globalWriteVec.empty()
       && !flowSet2.globalReadVec.empty()) {
    for (unsigned i = 0; i < flowSet1.globalWriteVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.globalReadVec.size(); j++) {
        if (flowSet1.globalWriteVec[i].relVal 
             == flowSet2.globalReadVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  if (!flowSet1.globalWriteVec.empty()
       && !flowSet2.globalWriteVec.empty()) {
    for (unsigned i = 0; i < flowSet1.globalWriteVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.globalWriteVec.size(); j++) {
        if (flowSet1.globalWriteVec[i].relVal 
             == flowSet2.globalWriteVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  return check;
}

static bool checkSharedFlowSet(RelFlowSet &flowSet1, RelFlowSet &flowSet2) {
  bool check = false;

  if (!flowSet1.sharedReadVec.empty()
       && !flowSet2.sharedWriteVec.empty()) {
    for (unsigned i = 0; i < flowSet1.sharedReadVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.sharedWriteVec.size(); j++) {
        if (flowSet1.sharedReadVec[i].relVal 
             == flowSet2.sharedWriteVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  if (!flowSet1.sharedWriteVec.empty()
       && !flowSet2.sharedReadVec.empty()) {
    for (unsigned i = 0; i < flowSet1.sharedWriteVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.sharedReadVec.size(); j++) {
        if (flowSet1.sharedWriteVec[i].relVal 
             == flowSet2.sharedReadVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  if (!flowSet1.sharedWriteVec.empty()
       && !flowSet2.sharedWriteVec.empty()) {
    for (unsigned i = 0; i < flowSet1.sharedWriteVec.size(); i++) {
      for (unsigned j = 0; j < flowSet2.sharedWriteVec.size(); j++) {
        if (flowSet1.sharedWriteVec[i].relVal 
             == flowSet2.sharedWriteVec[j].relVal) {
          check = true; 
          break;
        }
      }
      if (check) break;
    }
  }

  return check;
}

static bool existFlowSetConflict(std::set<Instruction*> &instSet1, 
                                 RelFlowSet &flowSet1, 
                                 std::set<Instruction*> &instSet2, 
                                 RelFlowSet &flowSet2, 
                                 bool glAndsh) {
  if (instSet1.empty())
    return false;
  else {
    // check flowSet1 and flowSet2
    if (flowSet1.empty())
      return false; 
    else {
      bool conflict = false;
      if (glAndsh) {
        conflict = checkGlobalFlowSet(flowSet1, flowSet2)
                     || checkSharedFlowSet(flowSet1, flowSet2);
      } else {
        conflict = checkGlobalFlowSet(flowSet1, flowSet2);
      }

      return conflict;
    }
  }
}

void CFGTree::dumpNodeInstForDFSChecking(CFGNode *node, 
                                         unsigned i) {
  std::cout << "set here in startDFSChecking, i: " 
            << i << std::endl;
  node->inst->dump();
}

// include the shared/global race checking within 
// the current BI 
bool CFGTree::startDFSCheckingForCurrentBI(CFGNode *node) {
  bool keepPath = false;

  if (node != NULL) {
    std::vector<CFGNode*> &treeNodes = node->cfgNodes;
    std::vector<CFGInstSet> &cfgInstSet = node->cfgInstSet;
 
    for (unsigned i = 0; i < treeNodes.size(); i++) {
      if (!cfgInstSet[i].explore) {
        bool singlePath = startDFSCheckingForCurrentBI(treeNodes[i]);

        if (!singlePath) {
          exploreNodeCurrentBI(node, singlePath, i, true);
          exploreNodeAcrossBI(node, singlePath, i, false);
        }
        else 
          cfgInstSet[i].explore = true;  
          
        keepPath = keepPath || singlePath; 
      } else {
        keepPath = true;
      }
    }

    // explore node's successor
    startDFSCheckingForCurrentBI(node->successor); 
  }

  return keepPath;
}

static void updateTaintNodeStr(CFGNode *node, std::string &str) {
  std::string tmp = "br-";
  bool set = false;
  if (node->tainted 
       && str.find("br-false-false") != std::string::npos) {

    if (node->causeIteration) {
      if (node->outOfIteration == 0)
        tmp += "true-false-ite";
      else 
        tmp += "false-true-ite";

      str = tmp;
    } else {
      for (unsigned i = 0; i < node->cfgInstSet.size(); i++) {
        if (node->cfgInstSet[i].instSet.empty()) {
          //std::cout << "sub path " << i 
          //          << " empty!" << std::endl;
          tmp += "false";
        } else {
          //std::cout << "sub path " << i 
          //          << " NOT empty!" << std::endl;
          if (!node->cfgFlowSet[i].empty()) {
            tmp += "true";
            set = true;
          } else {
            if (set) tmp += "false"; 
            else {
              tmp += "true";
              set = true;
            }
          }
        }

        if (i != node->cfgInstSet.size()-1)
          tmp += "-";
      }
      str = tmp;
    }
  }
}

static void annotateFunctionIR(LLVMContext &glContext, 
                               Function *f, 
                               CFGNode *node) {
  bool instFound = false;

  for (Function::iterator fi = f->begin(); fi != f->end(); fi++) {
    for (BasicBlock::iterator bi = fi->begin(); bi != fi->end(); bi++) {
      if (isTwoInstIdentical(bi, node->inst)) {
        Value *CI = MDString::get(glContext, "brprop");
        ArrayRef<Value*> temp = ArrayRef<Value*>(CI);
        MDNode *mdNode = MDNode::get(bi->getContext(), temp);

        std::string str = "br-";
        for (unsigned i = 0; i < node->cfgInstSet.size(); i++) {
          if (node->cfgInstSet[i].explore) {
            //std::cout << "branch " << i << ", explore! " << std::endl;
            str += "true";
          } else {
            //std::cout << "branch " << i << ", not explore! " << std::endl;
            str += "false";
          }

          if (i != node->cfgInstSet.size()-1)
            str += "-";
        }

        if (node->causeIteration) {
          //std::cout << "causeIteration br: " << std::endl;
          //node->inst->dump();
          str += "-ite";
        }

        updateTaintNodeStr(node, str);

        if (Verbose > 0) {
          std::cout << "The br inst: " << std::endl;
          node->inst->dump();
          std::cout << "Metadata: " << str << std::endl;
        }
        bi->setMetadata(str, mdNode);
        instFound = true;
        break;
      }
    }
    if (instFound) break;
  }
}

void CFGTree::exploreCFGTreeToAnnotate(LLVMContext &glContext, 
                                       Function *f, 
                                       CFGNode *node) {
  if (node) {
    //std::cout << "node inst: " << node->causeIteration << std::endl;
    //node->inst->dump();
    annotateFunctionIR(glContext, f, node);
    for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
      exploreCFGTreeToAnnotate(glContext, f, node->cfgNodes[i]);
    }
    exploreCFGTreeToAnnotate(glContext, f, node->successor);
  }
}

void CFGTree::setSyncthreadEncounter() {
  syncthreadEncounter = true;
  flowCurrent = NULL;
}

bool CFGTree::exploreOneSideOfNode(CFGInstSet &cfgInstSet, 
                                   RelFlowSet &relFlowSet, 
                                   CFGNode *node, bool glAndsh) {
  bool conflictFound = false;
  if (node) {
    for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
      conflictFound = exploreOneSideOfNode(cfgInstSet, relFlowSet,
                                           node->cfgNodes[i], glAndsh);
      if (!conflictFound) {
        conflictFound = existFlowSetConflict(cfgInstSet.instSet, 
                                             relFlowSet, 
                                             node->cfgInstSet[i].instSet, 
                                             node->cfgFlowSet[i], 
                                             glAndsh); 
        if (conflictFound) { 
          cfgInstSet.explore = true;
          node->cfgInstSet[i].explore = true;
        }
      } else {
        cfgInstSet.explore = true;
        node->cfgInstSet[i].explore = true;
      }
    }
  }
  return conflictFound;
}

// Check the ith path of "node"
void CFGTree::exploreNodeCurrentBI(CFGNode *node, bool &singlePath, 
                                   unsigned i, bool glAndsh) {
  CFGInstSet &cfgInstSet = node->cfgInstSet[i];
  RelFlowSet &flowSet = node->cfgFlowSet[i];

  CFGNode *tmp = node;
  do {
    // check the successor 
    if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                             tmp->succInstSet, 
                             tmp->succFlowSet, glAndsh)) {
      //dumpNodeInstForDFSChecking(node, i); 
      cfgInstSet.explore = true; 
      singlePath = true;
    } else {
      // explore back to the parent 
      CFGNode *parent = tmp->parent;
      if (parent) {
        for (unsigned j = 0; j < parent->cfgNodes.size(); j++) {
          if (parent->cfgNodes[j]) {
            if (parent->cfgNodes[j] == tmp) {
              if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                                       parent->cfgInstSet[j].instSet,
                                       parent->cfgFlowSet[j], glAndsh)) {
                //dumpNodeInstForDFSChecking(node, i); 
                cfgInstSet.explore = true;
                singlePath = true;
              }
            } else {
              if (exploreOneSideOfNode(cfgInstSet, flowSet, 
                                       parent->cfgNodes[j], glAndsh)) { 
                cfgInstSet.explore = true;
                singlePath = true;
              } else {
                if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                                         parent->cfgInstSet[j].instSet,
                                         parent->cfgFlowSet[j], 
                                         glAndsh)) {
                  parent->cfgInstSet[j].explore = true;
                  cfgInstSet.explore = true;
                  singlePath = true;
                }
              }
            }
          }
          if (singlePath) break;
        }
      } else {
        if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                                 preInstSet, preFlowSet, glAndsh)) {
          cfgInstSet.explore = true;
          singlePath = true;
        }
      }
    }
    tmp = tmp->parent;

  } while (tmp != NULL && tmp != flowCurrent->parent); 
}

void CFGTree::exploreNodeAcrossBI(CFGNode *node, 
                                  bool &singlePath, 
                                  unsigned i, 
                                  bool glAndsh) {
  CFGInstSet &cfgInstSet = node->cfgInstSet[i];
  RelFlowSet &flowSet = node->cfgFlowSet[i];

  CFGNode *tmp = flowCurrent->parent;

  while (tmp != NULL) {
    if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                             tmp->succInstSet, 
                             tmp->succFlowSet, glAndsh)) {
      cfgInstSet.explore = true;
      singlePath = true;
    } else {
      for (unsigned i = 0; i < tmp->cfgNodes.size(); i++) {
        if (tmp->cfgNodes[i]) {
          if (exploreOneSideOfNode(cfgInstSet, flowSet, 
                                   tmp->cfgNodes[i], glAndsh)) {
            cfgInstSet.explore = true;
            singlePath = true;
          } else {
            if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                                     tmp->cfgInstSet[i].instSet,
                                     tmp->cfgFlowSet[i], 
                                     glAndsh)) {
              tmp->cfgInstSet[i].explore = true;
              cfgInstSet.explore = true;
              singlePath = true;
            }
          }
        }
      }
    }
    tmp = tmp->parent;
  }

  if (existFlowSetConflict(cfgInstSet.instSet, flowSet, 
                           preInstSet, preFlowSet, glAndsh)) {
    cfgInstSet.explore = true;
    singlePath = true;
  }
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
