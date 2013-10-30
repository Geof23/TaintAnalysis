#include "llvm/Support/CommandLine.h"
#include "TaintAnalysis.h"
#include <fstream> 

/*This pass uses a combination of use def chain analysis with 
  Alias analysis to perform taint tracking in cuda kernels. 
  The taint sources are currently 
  set to cuda kernel thread configuration variables and kernel 
  input parameters */

namespace runtime {
  cl::opt<unsigned>
  Verbose("verbose",
          cl::desc("The verbosity level"),
          cl::init(0));
}

using namespace std;
using namespace taint;
using namespace runtime;

char TaintAnalysisCUDA::ID = 0;

RegisterPass<TaintAnalysisCUDA> Y("taint", "Taint analysis pass");

static std::string strip(std::string &in) {
  unsigned len = in.size();
  unsigned lead = 0, trail = len;
  while (lead<len && isspace(in[lead]))
    ++lead;
  while (trail>lead && isspace(in[trail-1]))
    --trail;
  return in.substr(lead, trail-lead);
}

static bool isTwoInstIdentical(llvm::Instruction *inst1, 
                               llvm::Instruction *inst2) {
  llvm::BasicBlock *bb1 = inst1->getParent();
  llvm::BasicBlock *bb2 = inst2->getParent();

  return (bb1 == bb2
           && inst1 == inst2);
}

VFunction::VFunction(llvm::Function *F) {
  unsigned numInstructions = 0;
  for (llvm::Function::iterator bbit = F->begin(),
       bbie = F->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = bbit;
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  }
  
  func = F;
  numInsts = numInstructions;
  insts = new VInstruction*[numInsts];
  curInst = insts;
  unsigned i = 0;

  for (llvm::Function::iterator bbit = F->begin(),
       bbie = F->end(); bbit != bbie; ++bbit) {
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end();
         it != ie; ++it) {
      VInstruction *vi = new VInstruction();
      vi->inst = it;
      insts[i++] = vi; 
    }
  }
}

VFunction::~VFunction() {
  for (unsigned i = 0; i < numInsts; i++)
    delete insts[i];
  delete[] insts;
}

void VFunction::restoreCurInst() {
  curInst = insts;
}

void VFunction::setCurrentInst(llvm::Instruction *inst) {
  for (unsigned i = 0; i < numInsts; i++) {
    if (isTwoInstIdentical(inst, insts[i]->inst)) {
      break;
    }
    curInst++;
  }
}

void VFunction::setCurrentInstThroughEntry(unsigned entry) {
  curInst = insts + entry;
}

void VFunction::dumpVFunctionInst() {
  for (unsigned i = 0; i < numInsts; i++) {
    std::cout << "inst " << i << ": " << std::endl;
    insts[i]->inst->dump();
  }
}

bool TaintAnalysisCUDA::doInitialization(llvm::Module &M) {
  const char* c_file = "kernelSet.txt";
  std::ifstream f(c_file);
  assert(f.is_open() && "unable to open kernelSet.txt file");

  while (!f.eof()) {
    std::string line;
    std::getline(f, line);
    line = strip(line);
    if (!line.empty())
      kernelSet.insert(std::make_pair(line, false));
  }
  f.close();

  curVFunc = NULL;

  // Identify the __shared__ global variables 
  for (Module::global_iterator gi = M.global_begin();
       gi != M.global_end(); ++gi) {
    llvm::GlobalValue *gv = dyn_cast<llvm::GlobalValue>(gi);

    if (gv && gv->hasSection()) {
      std::string sec = gv->getSection();
      if (sec == "__shared__") {
        sharedSet.push_back(SharedTaint(gv)); 
        unsigned size = sharedSet.size();
        for (Value::use_iterator ui = gv->use_begin(); 
             ui != gv->use_end(); ++ui) {
          Instruction *inst = dyn_cast<Instruction>(*ui);
          sharedSet[size-1].sharedInstSet.insert(inst);
        }
      }
    }
  }

  return false;
}

static Function* getTargetFunction(Value *calledVal) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv))
        return 0;

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;

    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

void TaintAnalysisCUDA::transferToBasicBlock(BasicBlock *dst) {
  unsigned entry = curVFunc->basicBlockEntry[dst]; 
  curVFunc->setCurrentInstThroughEntry(entry); 
}

void TaintAnalysisCUDA::handleBrInst(Instruction *inst, 
                                     std::vector<TaintArgInfo> &taintArgSet) {
  BranchInst *bi = dyn_cast<BranchInst>(inst);
  if (bi->isUnconditional()) {
    transferToBasicBlock(bi->getSuccessor(0));
  } else {
    Value *cond = bi->getCondition();
    bool brTainted = false;

    for (unsigned i = 0; i < taintArgSet.size(); i++) {
      //ExecutorUtil::dumpTaintInstList(taintArgSet[i].taintInstList);
      //ExecutorUtil::dumpTaintValueSet(taintArgSet[i].taintValueSet);
      if (ExecutorUtil::findValueFromTaintSet(cond, 
                                              taintArgSet[i].taintInstList, 
                                              taintArgSet[i].taintValueSet)) {
        // conditional is tainted, find the taint sink 
        taintArgSet[i].taintInstList.insert(inst);   
        taintArgSet[i].taint = true;
        brTainted = true;
        if (Verbose > 0) {
          TAINT_INFO2 << "The Br instruction is tainted w.r.t. the argument: " 
                      << taintArgSet[i].arg->getName().str()
                      << std::endl;
        } else {
          std::ofstream file("summary.txt", ios::app);
          if (file.is_open()) {
            file << "The Br instruction is tainted w.r.t. the argument: "
                 << taintArgSet[i].arg->getName().str() << "\n";
          }
          file.close();
        }
      }
    }

    if (!cfgTree->inIteration()) {
      // two branches are both possible 
      // Find the nearest post dominator as the reconvergence point     
      BasicBlock *postDom = ExecutorUtil::findNearestCommonPostDominator(inst, true); 
      CFGNode *node = new CFGNode(inst, postDom, 
                                  bi->getNumSuccessors(), true);
      if (brTainted)
        node->tainted = true;

      cfgTree->insertNodeIntoCFGTree(node);
      transferToBasicBlock(bi->getSuccessor(0));
    } else {
      cfgTree->exploreCFGUnderIteration(inst);
      CFGNode *current = cfgTree->getCurrentNode();
      if (current->causeIteration) {
        if (current->outOfIteration == 0) {
          // drop out of the iteration
          current->which++;
          transferToAnotherSideCurrentNode();
        } 
      } else 
        transferToBasicBlock(bi->getSuccessor(0));
    }
  }
}

void TaintAnalysisCUDA::transferToIterationPostDom(llvm::Instruction *inst) {
  if (Verbose > 0) {
    std::cout << "transferToIterationPostDom inst: " << std::endl;
    inst->dump();
  }
  BasicBlock *postDom = ExecutorUtil::findNearestCommonPostDominator(inst, true); 
  transferToBasicBlock(postDom);  
}

void TaintAnalysisCUDA::transferToAnotherSideCurrentNode() {
  CFGNode *curNode = cfgTree->getCurrentNode();
  if (curNode->isBrCond) {
    BranchInst *bi = dyn_cast<BranchInst>(curNode->inst);
    transferToBasicBlock(bi->getSuccessor(curNode->which));
  } else {
    SwitchInst *si = dyn_cast<SwitchInst>(curNode->inst);
    transferToBasicBlock(si->getSuccessor(curNode->which));
  }        
}

void TaintAnalysisCUDA::handleSwitchInst(Instruction *inst, 
                                         std::vector<TaintArgInfo> &taintArgSet) {
  SwitchInst *si = dyn_cast<SwitchInst>(inst); 
  Value *cond = si->getCondition();
   
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(cond,
                                            taintArgSet[i].taintInstList,
                                            taintArgSet[i].taintValueSet)) {
      // conditional is tainted, find the taint sink 
      taintArgSet[i].taintInstList.insert(inst);   
      taintArgSet[i].taint = true;
      if (Verbose > 0) {
        TAINT_INFO2 << "The Switch instruction is tainted w.r.t the argument: " 
                    << taintArgSet[i].arg->getName().str()
                    << std::endl;
      } else {
        std::ofstream file("summary.txt", ios::app);
        if (file.is_open()) {
          file << "The Switch instruction is tainted w.r.t. the argument: "
               << taintArgSet[i].arg->getName().str() << "\n";
        }
        file.close();
      }
    }
  }

  if (!cfgTree->inIteration()) {
    // two branches are both possible 
    BasicBlock *postDom = ExecutorUtil::findNearestCommonPostDominator(inst, false); 
    CFGNode *node = new CFGNode(inst, postDom, si->getNumSuccessors(), false); 
    cfgTree->insertNodeIntoCFGTree(node);
    transferToBasicBlock(si->getSuccessor(0));
  } else {
    cfgTree->exploreCFGUnderIteration(inst);
    transferToBasicBlock(si->getSuccessor(0));
  }
}

void TaintAnalysisCUDA::handlePHINode(Instruction *inst, 
                                      std::vector<TaintArgInfo> &taintArgSet) {
  PHINode *pi = dyn_cast<PHINode>(inst);

  for (unsigned i = 0; i < pi->getNumIncomingValues(); i++) {
    Value *val = pi->getIncomingValue(i);
    checkCFGTaintSetAffected(val, inst, false);  
  }

  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    for (unsigned j = 0; j < pi->getNumIncomingValues(); j++) {
      Value *val = pi->getIncomingValue(j);

      if (ExecutorUtil::findValueFromTaintSet(val, 
                                              taintArgSet[i].taintInstList, 
                                              taintArgSet[i].taintValueSet)) {
        taintArgSet[i].taintInstList.insert(inst);
        break;
      } 
    }
  }
}

void TaintAnalysisCUDA::handleSelectInst(Instruction *inst, 
                                         std::vector<TaintArgInfo> &taintArgSet) {
  SelectInst *si = dyn_cast<SelectInst>(inst);
  Value *cond = si->getCondition(); 

  checkCFGTaintSetAffected(cond, inst, false);

  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(cond, 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet)) {
      taintArgSet[i].taint = true;
      if (Verbose > 0) {
        TAINT_INFO2 << "The Select instruction is tainted w.r.t. argument: " 
                    << taintArgSet[i].arg->getName().str() 
                    << std::endl;
      } else {
        std::ofstream file("summary.txt", ios::app);
        if (file.is_open()) {
          file << "The Select instruction is tainted w.r.t. the argument: "
               << taintArgSet[i].arg->getName().str() << "\n";
        }
        file.close();
      }
    }

    if (ExecutorUtil::findValueFromTaintSet(si->getTrueValue(), 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet) 
         || ExecutorUtil::findValueFromTaintSet(si->getFalseValue(),
                                                taintArgSet[i].taintInstList,
                                                taintArgSet[i].taintValueSet)) {
      taintArgSet[i].taintInstList.insert(inst);   
    }
  }
}

static bool isCUDAArithmeticIntrinsic(std::string fName) {
  return (fName.find("mulhi") != std::string::npos
          || fName.find("mul64hi") != std::string::npos
          || fName.find("mul24") != std::string::npos 
          || fName.find("sad") != std::string::npos 
          || fName.find("fdivide") != std::string::npos
          || fName.compare("__sinf") == 0
          || fName.compare("__cosf") == 0
          || fName.compare("__tanf") == 0
          || fName.compare("sinf") == 0
          || fName.compare("cosf") == 0
          || fName.compare("tanf") == 0
          || fName.compare("sin") == 0
          || fName.compare("cos") == 0
          || fName.compare("tan") == 0
          || fName.find("sinpi") != std::string::npos
          || fName.find("cospi") != std::string::npos
          || fName.find("exp") != std::string::npos
          || fName.find("log") != std::string::npos
          || fName.find("pow") != std::string::npos
          || fName.find("min") != std::string::npos
          || fName.find("max") != std::string::npos
          || fName.find("__fadd_") != std::string::npos
          || fName.find("__dadd_") != std::string::npos
          || fName.find("__fmul_") != std::string::npos
          || fName.find("__dmul_") != std::string::npos
          || fName.find("fma") != std::string::npos
          || fName.find("rcp") != std::string::npos
          || fName.find("sqrt") != std::string::npos
          || fName.find("__fdiv_") != std::string::npos
          || fName.find("__ddiv_") != std::string::npos
          || fName.find("clz") != std::string::npos
          || fName.find("ffs") != std::string::npos
          || fName.find("popc") != std::string::npos
          || fName.find("brev") != std::string::npos
          || fName.find("byte_perm") != std::string::npos
          || fName.find("hadd") != std::string::npos
          || fName.find("abs") != std::string::npos
          || fName.find("saturate") != std::string::npos
          || fName.find("round") != std::string::npos
          || fName.find("trunc") != std::string::npos
          || fName.find("floor") != std::string::npos
          || fName.find("ceil") != std::string::npos
          || fName.find("fmod") != std::string::npos);
}

static bool isCUDAConversionIntrinsic(std::string fName) {
  return (fName.find("__float2int_") != std::string::npos
          || fName.find("__float2uint_") != std::string::npos
          || fName.find("__int2float_") != std::string::npos
          || fName.find("__uint2float_") != std::string::npos
          || fName.find("__float2ll_") != std::string::npos
          || fName.find("__float2ull_") != std::string::npos
          || fName.find("__ll2float_") != std::string::npos
          || fName.find("__ull2float_") != std::string::npos
          || fName.find("__float2half_") != std::string::npos
          || fName.find("__half2float") != std::string::npos
          || fName.find("__int2double_") != std::string::npos
          || fName.find("__uint2double_") != std::string::npos
          || fName.find("__ll2double_") != std::string::npos
          || fName.find("__ull2double_") != std::string::npos
          || fName.find("__double2int_") != std::string::npos
          || fName.find("__double2uint_") != std::string::npos
          || fName.find("__double2ll_") != std::string::npos
          || fName.find("__double2ull_") != std::string::npos
          || fName.find("__double2hiint_") != std::string::npos
          || fName.find("__double2loint_") != std::string::npos
          || fName.find("__hiloint2double") != std::string::npos
          || fName.find("__float_as_int") != std::string::npos
          || fName.find("__int_as_float") != std::string::npos
          || fName.find("__double_as_longlong") != std::string::npos
          || fName.find("__longlong_as_double") != std::string::npos); 

} 

static bool isCUDAAtomicIntrinsic(std::string fName) {
  return (fName.find("AtomicAdd") != std::string::npos
          || fName.find("AtomicExch") != std::string::npos
          || fName.find("AtomicMin") != std::string::npos
          || fName.find("AtomicMax") != std::string::npos
          || fName.find("AtomicInc") != std::string::npos
          || fName.find("AtomicDec") != std::string::npos
          || fName.find("AtomicCas") != std::string::npos
          || fName.find("AtomicAnd") != std::string::npos
          || fName.find("AtomicOr") != std::string::npos
          || fName.find("AtomicXor") != std::string::npos);
}

void TaintAnalysisCUDA::executeCall(Instruction *inst, 
                                    Function *f, 
                                    std::vector<TaintArgInfo> &taintArgSet, 
                                    AliasAnalysis &AA) {
  return;
}

void TaintAnalysisCUDA::executeCUDAArithOrConvIntrinsic(Instruction *inst, 
                                                        std::string fName,
                                                        std::vector<TaintArgInfo> &taintArgSet) {
  bool explore = false;
  for (unsigned i = 0; i < inst->getNumOperands(); i++) {
    Value *arg = inst->getOperand(i);
    explore = checkCFGTaintSetAffected(arg, inst, false); 
    if (explore) break;
  }
  // check taint set 
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    for (unsigned j = 0; j < inst->getNumOperands(); j++) {
      Value *arg = inst->getOperand(j);
      if (ExecutorUtil::findValueFromTaintSet(arg, 
                                              taintArgSet[i].taintInstList, 
                                              taintArgSet[i].taintValueSet)) {
        taintArgSet[i].taintInstList.insert(inst);
        break;
      } 
    }
  }
}

void TaintAnalysisCUDA::executeCUDAAtomicIntrinsic(Instruction *inst, 
                                                   std::string fName,
                                                   std::vector<TaintArgInfo> &taintArgSet) {
  // check cfgTree ... 
  bool explore = false;

  for (unsigned i = 0; i < inst->getNumOperands(); i++) {
    Value *arg = inst->getOperand(i);
    explore = checkCFGTaintSetAffected(arg, inst, true); 
    if (explore) break;
  }
  // check taint set ... 
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    for (unsigned j = 0; j < inst->getNumOperands(); j++) {
      Value *arg = inst->getOperand(j);
      if (ExecutorUtil::findValueFromTaintSet(arg, 
                                              taintArgSet[i].taintInstList, 
                                              taintArgSet[i].taintValueSet)) {
        taintArgSet[i].taintInstList.insert(inst);
    
        if (fName.find("AtomicMin") != std::string::npos 
             || fName.find("AtomicMax") != std::string::npos
               || fName.find("AtomicCas") != std::string::npos) {
          if (Verbose > 0) {
            TAINT_INFO2 << "The argument in Atomic{Min,Max,Cas} is tainted" 
                        << " w.r.t. argument: " 
                        << taintArgSet[i].arg->getName().str()
                        << std::endl;
          } else {
            std::ofstream file("summary.txt", ios::app);
            if (file.is_open()) {
              file << "The argument in Atomic{Min,Max,Cas} is tainted "
                   << "w.r.t. the argument: "
                   << taintArgSet[i].arg->getName().str() << "\n";
            }
            file.close();
          }
          taintArgSet[i].taint = true;
        }
        break;
      }
    }
  }
}

void TaintAnalysisCUDA::executeCUDAIntrinsic(Instruction *inst,
                                             Function *f, 
                                             std::vector<TaintArgInfo> &taintArgSet) {
  std::string fName = f->getName().str();

  if (isCUDAArithmeticIntrinsic(fName)
       || isCUDAConversionIntrinsic(fName)) {
    executeCUDAArithOrConvIntrinsic(inst, fName, taintArgSet);
  } else if (isCUDAAtomicIntrinsic(fName)) {
    executeCUDAAtomicIntrinsic(inst, fName, taintArgSet);
  } 
}

void TaintAnalysisCUDA::handleArithmeticInst(Instruction *inst, 
                                             std::vector<TaintArgInfo> &taintArgSet) { 
  Value *left = inst->getOperand(0);    
  Value *right = inst->getOperand(1);    

  // check CFG tree
  checkCFGTaintSetAffected(left, inst, false);
  checkCFGTaintSetAffected(right, inst, false);

  // check taint set 
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(left, 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet) 
         || ExecutorUtil::findValueFromTaintSet(right,
                                                taintArgSet[i].taintInstList, 
                                                taintArgSet[i].taintValueSet))
      taintArgSet[i].taintInstList.insert(inst);
  }

  // check shared set
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(left, 
                                            sharedSet[i].sharedInstSet, 
                                            sharedSet[i].sharedValueSet)
         || ExecutorUtil::findValueFromTaintSet(right,   
                                                sharedSet[i].sharedInstSet,    
                                                sharedSet[i].sharedValueSet)) {
      sharedSet[i].sharedInstSet.insert(inst);
    }
  }
}

void TaintAnalysisCUDA::handleCmpInst(Instruction *inst, 
                                      std::vector<TaintArgInfo> &taintArgSet) {
  Value *left = inst->getOperand(0); 
  Value *right = inst->getOperand(1); 

  // check CFG tree
  checkCFGTaintSetAffected(left, inst, false);
  checkCFGTaintSetAffected(right, inst, false);

  // check taint set
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(left, 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet) 
         || ExecutorUtil::findValueFromTaintSet(right, 
                                                taintArgSet[i].taintInstList, 
                                                taintArgSet[i].taintValueSet))
    taintArgSet[i].taintInstList.insert(inst);
  }
}

bool ExecutorUtil::findValueFromTaintSet(Value *val, 
                                         std::set<Instruction*> &taintInstList, 
                                         std::set<Value*> &taintValueSet) {
  if (Instruction *si = dyn_cast<Instruction>(val)) {
    if (taintInstList.find(si) != taintInstList.end()) {
      if (Verbose > 0) {
        dumpTaintInstList(taintInstList);
        dumpTaintValueSet(taintValueSet);
      }
      return true;
    }
  } else {
    if (taintValueSet.find(val) != taintValueSet.end()) {
      if (Verbose > 0) {
        dumpTaintInstList(taintInstList);
        dumpTaintValueSet(taintValueSet);
      }
      return true;
    } else {
      if (taintValueSet.find(val->stripPointerCasts()) 
                               != taintValueSet.end()) {
        return true;
      }
    }
  }
  return false;
}

BasicBlock* ExecutorUtil::findNearestCommonPostDominator(llvm::Instruction *inst, 
                                                         bool isCondBr) {
  llvm::PostDominatorTree *postDomTree = (llvm::PostDominatorTree*)llvm::createPostDomTree();
  BasicBlock *postDomBB = NULL;
  llvm::Function *fn = inst->getParent()->getParent();
  BasicBlock *BB1 = NULL;
  BasicBlock *BB2 = NULL;

  if (isCondBr) {
    BranchInst *bi = cast<BranchInst>(inst);
    BB1 = bi->getSuccessor(0);
    BB2 = bi->getSuccessor(1);
  } else {
    SwitchInst *si = cast<SwitchInst>(inst);
    assert(si->getNumSuccessors() >= 2 && "Number of successors smaller than 2!\n");
    // pick two successors
    BB1 = si->getSuccessor(0);
    BB2 = si->getSuccessor(1);
  }

  postDomTree->runOnFunction(*fn);
  postDomBB = postDomTree->findNearestCommonDominator(BB1, BB2);

  return postDomBB;
}

void ExecutorUtil::dumpTaintInstList(std::set<Instruction*> &taintInstList) {
  if (taintInstList.size())
    TAINT_INFO2 << "Dump TaintInstList: " << std::endl;
  unsigned i = 0;
  for (std::set<Instruction*>::iterator si = taintInstList.begin();
       si != taintInstList.end(); si++, i++) {
    TAINT_INFO2 << "TaintInstList[" << i << "]: " << std::endl;
    (*si)->dump();
  }
}

void ExecutorUtil::dumpTaintValueSet(std::set<Value*> &taintValueSet) {
  if (taintValueSet.size())
    TAINT_INFO2 << "Dump TaintValueSet: " << std::endl;
  unsigned i = 0;
  for (std::set<Value*>::iterator si = taintValueSet.begin(); 
       si != taintValueSet.end(); si++, i++) {
    TAINT_INFO2 << "TaintValueSet[" << i << "]: " << std::endl; 
    (*si)->dump();
  }
}

void TaintAnalysisCUDA::handleLoadInst(Instruction *inst, 
                                       std::vector<TaintArgInfo> &taintArgSet, 
                                       AliasAnalysis &AA) {
  LoadInst *load = dyn_cast<LoadInst>(inst); 
  Value *pointer = load->getPointerOperand(); 
 
  // check taint set 
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(pointer, 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet)) {
      taintArgSet[i].taintInstList.insert(inst);
    }
  }
  // check shared set
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (inst->getType()->isPointerTy()
         && ExecutorUtil::findValueFromTaintSet(pointer, 
                                                sharedSet[i].sharedInstSet, 
                                                sharedSet[i].sharedValueSet)) {
      sharedSet[i].sharedInstSet.insert(inst);
    }
  }
}

void TaintAnalysisCUDA::handlePointerOperand(Instruction *inst,
                                             std::set<Instruction*> &instSet, 
                                             std::set<Value*> &valueSet) {
  unsigned num = inst->getNumOperands();

  for (unsigned i = 0; i < num; i++) {
    Value *op = inst->getOperand(i);

    if (op->getType()->isPointerTy()) {
      if (Instruction *i = dyn_cast<Instruction>(op)) {
        handlePointerOperand(i, instSet, valueSet);
      } else {
        valueSet.insert(op);
      }
    }
  }

  instSet.insert(inst);
}

void TaintAnalysisCUDA::handleStoreInst(Instruction *inst, 
                                        std::vector<TaintArgInfo> &taintArgSet,
                                        AliasAnalysis &AA) {
  StoreInst *store = dyn_cast<StoreInst>(inst);
  Value *valueOp = store->getValueOperand();
  Value *pointerOp = store->getPointerOperand();
 
  // check taint set
  for (std::vector<TaintArgInfo>::iterator vi = taintArgSet.begin(); 
       vi != taintArgSet.end(); vi++) {
    // If value is tainted, then we set the address referring 
    // to this value as tainted 
    if (ExecutorUtil::findValueFromTaintSet(valueOp, 
                                            vi->taintInstList, 
                                            vi->taintValueSet)) {
      if (Instruction *i = dyn_cast<Instruction>(pointerOp))
        handlePointerOperand(i, vi->taintInstList, vi->taintValueSet);
      else
        vi->taintValueSet.insert(pointerOp);

      vi->taintInstList.insert(inst);
    }
  }

  // check shared set
  for (std::vector<SharedTaint>::iterator vi = sharedSet.begin(); 
       vi != sharedSet.end(); vi++) {
    if (valueOp->getType()->isPointerTy()
         && ExecutorUtil::findValueFromTaintSet(valueOp, 
                                                vi->sharedInstSet, 
                                                vi->sharedValueSet)) {
      if (Instruction *i = dyn_cast<Instruction>(pointerOp))
        handlePointerOperand(i, vi->sharedInstSet, vi->sharedValueSet);
      else
        vi->sharedValueSet.insert(pointerOp);

      vi->sharedInstSet.insert(inst);
    }
  }
}

bool TaintAnalysisCUDA::checkCFGTaintSetAffected(Value *val, 
                                                 Instruction *inst,
                                                 bool sSink) {
  bool explore = false;

  if (Instruction *si = dyn_cast<Instruction>(val)) {
    // check if inst will be affected by instruction in the exploredCFGInst
    for (std::map<CFGNode*, std::vector<CFGTaintSet> >::iterator mi = exploredCFGInst.begin(); 
         mi != exploredCFGInst.end(); mi++) {
      std::vector<CFGTaintSet> &cfgTaintVec = mi->second;
      for (unsigned i = 0; i < cfgTaintVec.size(); i++) {
        if (!cfgTaintVec[i].explore
             && cfgTaintVec[i].instSet.find(si) != cfgTaintVec[i].instSet.end()) {
          cfgTaintVec[i].instSet.insert(inst);
          explore = true;
          if (sSink) {
            if (Verbose > 0) {
              // explore is set true, and update the CFGTree 
              std::cout << "The instruction used in the sensitive sinks: " 
                        << std::endl;
              inst->dump();
            }
            cfgTaintVec[i].explore = true;
            CFGNode *node = mi->first;
            node->cfgInstSet[i].explore = true; 
          }
        }
      }
    }
  }

  return explore;
} 

void TaintAnalysisCUDA::checkGEPIIndex(Instruction *inst, 
                                       std::vector<TaintArgInfo> &taintArgSet) {
  GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(inst);
  bool explore = false;

  // To test other arguments are tainted or not  
  for (llvm::User::op_iterator oi = gepi->idx_begin(); 
       oi != gepi->idx_end(); oi++) {
    Value *element = dyn_cast<Value>(oi);
    for (unsigned i = 0; i < taintArgSet.size(); i++) {
      if (ExecutorUtil::findValueFromTaintSet(element, 
                                              taintArgSet[i].taintInstList, 
                                              taintArgSet[i].taintValueSet)) {
        if (Verbose > 0) {
          TAINT_INFO2 << "The index is tainted, the index: " << std::endl;
          element->dump(); 
        } else {
          std::ofstream file("summary.txt", ios::app);
          if (file.is_open()) {
            file << "The index is tainted w.r.t. the argument: "
                 << taintArgSet[i].arg->getName().str() << "\n";
          }
          file.close();
        }
        taintArgSet[i].taint = true;
      }
    }

    if (!explore)
      explore = checkCFGTaintSetAffected(element, inst, true);
  }
}

void TaintAnalysisCUDA::handleGetElementPtrInst(Instruction *inst, 
                                                std::vector<TaintArgInfo> &taintArgSet,
                                                AliasAnalysis &AA) {
  GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(inst); 
  Value *pointer = gepi->getPointerOperand();
  bool device_alias = false;
  bool shared_alias = false;

  // check cfgTree ... 
  checkCFGTaintSetAffected(pointer, inst, false);
 
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    device_alias = ExecutorUtil::findValueFromTaintSet(pointer, 
                                                       taintArgSet[i].taintInstList, 
                                                       taintArgSet[i].taintValueSet);
    // the pointer value is the alias of "global" value
    if (device_alias) {
      taintArgSet[i].taintInstList.insert(inst);
      break;
    } else {
      if (!isa<Instruction>(pointer)) {
        Value *stripVal = pointer->stripPointerCasts();
       
        device_alias = ExecutorUtil::findValueFromTaintSet(stripVal, 
                                                           taintArgSet[i].taintInstList, 
                                                           taintArgSet[i].taintValueSet);
        if (device_alias) {
          taintArgSet[i].taintInstList.insert(inst);
          break;
        }
      }
    }
  }

  for (unsigned i = 0; i < sharedSet.size(); i++) {
    shared_alias = ExecutorUtil::findValueFromTaintSet(pointer, 
                                                       sharedSet[i].sharedInstSet, 
                                                       sharedSet[i].sharedValueSet);
    // the pointer value is the alias of "shared" value
    if (shared_alias) {
      sharedSet[i].sharedInstSet.insert(inst);
      break;
    }
  }

  if (device_alias || shared_alias)
    checkGEPIIndex(inst, taintArgSet);
}

void TaintAnalysisCUDA::handleConversionInst(Instruction *inst, 
                                             std::vector<TaintArgInfo> &taintArgSet) {
  Value *val = inst->getOperand(0); 

  checkCFGTaintSetAffected(val, inst, false);

  // check taint set
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(val, 
                                            taintArgSet[i].taintInstList, 
                                            taintArgSet[i].taintValueSet)) {
      taintArgSet[i].taintInstList.insert(inst);
    }
  }

  // check shared set
  for (unsigned i = 0; i < sharedSet.size(); i++) {
    if (ExecutorUtil::findValueFromTaintSet(val, 
                                            sharedSet[i].sharedInstSet, 
                                            sharedSet[i].sharedValueSet)) { 
      sharedSet[i].sharedInstSet.insert(inst);
    }
  } 
}

// Return block is changed or not 
bool TaintAnalysisCUDA::executeInstruction(llvm::Instruction *inst,
                                           std::vector<TaintArgInfo> &taintArgSet,
                                           AliasAnalysis &AA) {
  bool blockChange = false;

  switch (inst->getOpcode()) {
    case Instruction::Alloca: {
      break;
    }
    case Instruction::Ret: {
      // return inst
      blockChange = true;
      break;
    }
    case Instruction::Br: {
      handleBrInst(inst, taintArgSet);
      blockChange = true;
      break;
    }
    case Instruction::Switch: {
      handleSwitchInst(inst, taintArgSet);
      blockChange = true;
      break;
    }
    case Instruction::Invoke:
    case Instruction::Call: {
      CallSite cs(inst);
      Value *fp = cs.getCalledValue();
      Function *f = getTargetFunction(fp);
      std::string fName = f->getName().str();
      if (f) {
        if (!f->isDeclaration()) {
          // Non-declaration 
          executeCall(inst, f, taintArgSet, AA);
        } else {
          executeCUDAIntrinsic(inst, f, taintArgSet);
        }
      }
      break;
    }
    case Instruction::PHI: {
      handlePHINode(inst, taintArgSet);
      break;
    }
    case Instruction::Select: {
      handleSelectInst(inst, taintArgSet);
      break;
    }
    // Arithmetic / logical (Integer & Floating point)
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::FAdd: 
    case Instruction::FSub: 
    case Instruction::FMul: 
    case Instruction::FDiv: 
    case Instruction::FRem: {
      // If one of operands refers the value, then the result of 
      // this instruction refers the value too 
      handleArithmeticInst(inst, taintArgSet);
      break;
    }
    // Compare 
    case Instruction::ICmp: 
    case Instruction::FCmp: {
      handleCmpInst(inst, taintArgSet);
      break;
    }
    // Memory instructions...
    case Instruction::Load: {
      handleLoadInst(inst, taintArgSet, AA);
      break;
    }
    case Instruction::Store: {
      handleStoreInst(inst, taintArgSet, AA);
      break;
    }
    case Instruction::GetElementPtr: {
      handleGetElementPtrInst(inst, taintArgSet, AA);
      break;
    }
    // conversions (Integer & Floating point)
    case Instruction::Trunc: 
    case Instruction::ZExt: 
    case Instruction::SExt: 
    case Instruction::IntToPtr: 
    case Instruction::PtrToInt: 
    case Instruction::BitCast: 
    case Instruction::FPTrunc:
    case Instruction::FPExt:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::UIToFP:
    case Instruction::SIToFP: {
      handleConversionInst(inst, taintArgSet);
      break; 
    }
    default: {
      std::cout << "unsupported inst encountered!" << std::endl;
      std::cout << "inst opcode: " << inst->getOpcodeName() << std::endl;
      inst->dump();
      break;
    }
  }

  return blockChange;
} 

static bool isReturnInst(llvm::Instruction *inst) {
  return inst->getOpcode() == Instruction::Ret; 
}

static bool allKernelsExplored(std::map<std::string, bool> &kernelSet) {
  for (std::map<std::string, bool>::iterator it = kernelSet.begin();
       it != kernelSet.end(); it++) {
    if (!it->second) 
      return false; 
  }
  return true;
}

static void extractInstFromSourceCode(MDNode *N) {
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

void TaintAnalysisCUDA::dumpTaintArgInfo(TaintArgInfo &argInfo) {
  TAINT_INFO2 << "In function [ " << argInfo.fName 
              << "], the " << argInfo.argNum << " argument: " 
              << std::endl;
  argInfo.arg->dump();

  std::set<Instruction*> &taintInstList = argInfo.taintInstList;
  for (std::set<Instruction*>::iterator si = taintInstList.begin(); 
       si != taintInstList.end(); si++) {
    TAINT_INFO2 << "Inst: " << std::endl;    
    if (MDNode *N = (*si)->getMetadata("dbg")) {  
      // Here I is an LLVM instruction
      extractInstFromSourceCode(N);
      (*si)->dump();
    } else {
      (*si)->dump();
    }
  }
}

static bool existTaintInArgTaintSet(std::vector<TaintArgInfo> &taintArgSet, 
                                    unsigned &num) {
  bool taint = false;
  for (unsigned i = 0; i < taintArgSet.size(); i++) {
    if (taintArgSet[i].taint) {
      taint = true;
      num++;
    }
  }
  return taint;
}

bool TaintAnalysisCUDA::dumpAliasResult(Value *pointer, AliasAnalysis &AA, 
                                        std::vector<Value*> &sharedSet, 
                                        unsigned &num) {
  bool alias = false;

  for (unsigned i = 0; i < sharedSet.size(); i++) {
    AliasAnalysis::AliasResult res = AA.alias(sharedSet[i], pointer);

    switch(res) {
      case 0: 
        break;
      case 1:
        break;
      case 2:
        alias = true;
        num = i;
        break;
      case 3:
        alias = true;
        num = i;
        break;
    }

    if (alias) break; 
  }

  return alias;
}

void TaintAnalysisCUDA::encounterSyncthreadsBarrier(Instruction *inst) {
  if (!cfgTree->inIteration()) {
    if (cfgTree->getFlowCurrentNode()) {
      if (inst->getOpcode() == Instruction::Invoke 
           || inst->getOpcode() == Instruction::Call
             || inst->getOpcode() == Instruction::Ret) {
        if (inst->getOpcode() == Instruction::Invoke 
             || inst->getOpcode() == Instruction::Call) {
          // __syncthreads, end of the stage
          CallSite cs(inst);
          Value *fp = cs.getCalledValue();
          Function *f = getTargetFunction(fp);
          std::string fName = f->getName().str();
          if (fName.find("__syncthreads") != std::string::npos) {
            // start checking  
            CFGNode *flowCurrent = cfgTree->getFlowCurrentNode();  
            cfgTree->startDFSCheckingForCurrentBI(flowCurrent); 
            cfgTree->setSyncthreadEncounter();
          }
        } else {
          CFGNode *flowCurrent = cfgTree->getFlowCurrentNode();
          cfgTree->startDFSCheckingForCurrentBI(flowCurrent);
        }
      }
    }
  }
}

void TaintAnalysisCUDA::constructExploredCFGInst() {
  if (!cfgTree->inIteration()) {
    CFGNode *node = cfgTree->getCurrentNode();
    unsigned which = node->which;
    if (exploredCFGInst.find(node) == exploredCFGInst.end()) {
      std::vector<CFGTaintSet> cfgTaintSet;
      cfgTaintSet.push_back(CFGTaintSet(node->cfgInstSet[which-1]));
      exploredCFGInst.insert(std::make_pair(node, cfgTaintSet));  
    } else {
      std::vector<CFGTaintSet> &cfgTaintSet = 
                                     exploredCFGInst.find(node)->second;
      cfgTaintSet.push_back(CFGTaintSet(node->cfgInstSet[which-1]));
    }
  }
}

void TaintAnalysisCUDA::insertCurInstToCFGTree(Instruction *inst,
                                               std::vector<TaintArgInfo> &taintArgSet, 
                                               AliasAnalysis &AA) {
  if (!cfgTree->inIteration()) {
    if (cfgTree->getCurrentNode()) {
      cfgTree->insertCurInst(inst, taintArgSet, AA, sharedSet);
    } else {
      cfgTree->preInstSet.insert(inst);

      if (inst->getOpcode() == Instruction::Load) 
        ExecutorUtil::checkLoadInst(inst, taintArgSet, sharedSet, 
                                    AA, cfgTree->preFlowSet);

      if (inst->getOpcode() == Instruction::Store)
        ExecutorUtil::checkStoreInst(inst, taintArgSet, sharedSet, 
                                     AA, cfgTree->preFlowSet);
    }
  }
}

// include the __global__ and __device__ kernels  
bool TaintAnalysisCUDA::exploreCUDAKernel(Function *f, 
                                          AliasAnalysis &AA) {
  // local dafalseta structures which are populated for each function
  // iterate through the paremeter list of the kernel
  std::vector<TaintArgInfo> taintArgSet;
  unsigned totalArgNum = 0;
  cfgTree = new CFGTree();

  if (Verbose > 0) {
    TAINT_INFO2 << "****************************************"
                << std::endl;
  } else {
    std::ofstream file("summary.txt", ios::app);
    if (file.is_open()) {
      file << "****************************************"
           << std::endl;
    }
    file.close();
  }

  for (Function::arg_iterator ai = f->arg_begin();
       ai != f->arg_end(); ++ai, ++totalArgNum) {
    Value *arg = dyn_cast<Value>(ai);
    if (arg->getType()->isPointerTy()) {
      if (Verbose > 0) {
        TAINT_INFO2 << "The " << totalArgNum 
                    << " (pointer) argument of function " 
                    << f->getName().str() << ": " << std::endl;
        arg->dump();
      } else {
        std::ofstream file("summary.txt", ios::app);
        if (file.is_open()) {
          file << "The " << totalArgNum 
               << " (pointer) argument of function " 
               << f->getName().str() << ": " << std::endl;
          file << arg->getName().str() 
               << std::endl;
        }
        file.close();
      }

      TaintArgInfo argInfo(f->getName().str(), arg, false, totalArgNum);
      taintArgSet.push_back(argInfo);

      unsigned size = taintArgSet.size();
      taintArgSet[size-1].taintValueSet.insert(arg);
    }
  }

  if (Verbose > 0) {
    std::cout << std::endl;
    TAINT_INFO2 << "Start evaluating " << taintArgSet.size() 
                << " (pointer) arguments of function " 
                << f->getName().str() 
                << std::endl;
  } else {
    std::ofstream file("summary.txt", ios::app);
    if (file.is_open()) {
      file << std::endl;
      file << "Start evaluating " << taintArgSet.size() 
           << " (pointer) arguments of function " << f->getName().str() 
           << std::endl;
    }
    file.close();
  }

  curVFunc->stepInstruction();

  bool blockChange = false;
  while (true) {
    Instruction *inst = curVFunc->getCurrentInst();
    if (Verbose > 0) {
      std::cout << "\nget current inst: " << std::endl;
      inst->dump();
    }

    if (!cfgTree->isCFGTreeFullyExplored()) {
      // To determine if this instruction resides in the Basic Block
      // that is the post-dominator
      bool finishIteration = false;
      blockChange = cfgTree->updateCFGTree(inst, taintArgSet,
                                           exploredBBSet, 
                                           blockChange, 
                                           finishIteration);
      if (finishIteration) {
        transferToIterationPostDom(inst);
        continue;
      } else {
        if (blockChange) {
          transferToAnotherSideCurrentNode();
          constructExploredCFGInst();
          continue;
        }
      }
    } 

    blockChange = executeInstruction(inst, taintArgSet, AA);
    insertCurInstToCFGTree(inst, taintArgSet, AA);
    encounterSyncthreadsBarrier(inst);

    BasicBlock *bb = inst->getParent();
    exploredBBSet.insert(bb);

    if (!blockChange)
      curVFunc->stepInstruction();

    if (isReturnInst(inst))
      break;
  }

  unsigned num = 0;
  bool taintSink = existTaintInArgTaintSet(taintArgSet, num);

  if (!taintSink) {
    if (Verbose > 0) {
      TAINT_INFO2 << "\n+++In the kernel " << f->getName().str() 
                  << ", no need to set its " 
                  << totalArgNum << " arguments as [Tainted]+++"
                  << std::endl;
    } else {
      std::ofstream file("summary.txt", ios::app);
      if (file.is_open()) {
        file << "\nIn the kernel " << f->getName().str() 
             << ", no need to set its " 
             << totalArgNum << " arguments as [Tainted]"
             << std::endl;
      }
      file << "=====================================" << std::endl;
      file.close();
    }
  } else {
    if (Verbose > 0) {
      TAINT_INFO2 << "\nIn the kernel " << f->getName().str() 
                  << ", have to set " << num << " arguments over "
                  << totalArgNum << " arguments as [Tainted]"
                  << std::endl;

      for (unsigned i = 0; i < taintArgSet.size(); i++) {
        if (taintArgSet[i].taint) {
          TAINT_INFO2 << "The " << i << " argument: " << std::endl;
          dumpTaintArgInfo(taintArgSet[i]);
        }
      }
      TAINT_INFO2 << "=====================================" << std::endl;
    } else {
      std::ofstream file("summary.txt", ios::app);
      if (file.is_open()) {
        file << std::endl;
        file << "\nIn the kernel " << f->getName().str() 
             << ", have to set " << num << " arguments over "
             << totalArgNum << " arguments as [Tainted]"
             << std::endl;
      }
      for (unsigned i = 0; i < taintArgSet.size(); i++) {
        if (taintArgSet[i].taint) {
          file << "The " << i << " argument: " 
               << taintArgSet[i].arg->getName().str()
               << std::endl;
          file << "=====================================" << std::endl;
        }
      }
      file.close();
    }
  }

  cfgTree->exploreCFGTreeToAnnotate(getGlobalContext(), 
                                    f, cfgTree->getRootNode());

  taintArgSet.clear();
  delete cfgTree;
  return false; 
}

bool TaintAnalysisCUDA::runOnFunction(llvm::Function &F) {
  AliasAnalysis &AA = getAnalysis<AliasAnalysis>();

  std::string fName = F.getName().str();
  if (kernelSet.find(fName) == kernelSet.end()) {
    // do not explore the function 
    // which is not in the kernel list
    return true;
  }

  VFunction *vfunc = new VFunction(&F);
  curVFunc = vfunc;
  functions.push_back(vfunc);
  
  // The entry for exploring  __global__ function
  exploreCUDAKernel(&F, AA);
  kernelSet.find(fName)->second = true;
  
  if (allKernelsExplored(kernelSet)) {
    if (Verbose > 0) {
      TAINT_INFO2 << "All kernels are explored" << std::endl;
    }
    for (std::vector<VFunction*>::iterator it = functions.begin(); 
         it != functions.end(); it++) {
      delete *it;
    }
  }

  return false;
}
