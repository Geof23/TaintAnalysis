#pragma once

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Value.h"
#include "llvm/MDBuilder.h"
#include "llvm/BasicBlock.h"
#include "llvm/Module.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/GlobalValue.h"
#include "llvm/User.h"
#include "llvm/Argument.h"
#include "llvm/InitializePasses.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/CallSite.h"
#include "llvm/PassSupport.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/DebugInfo.h"

#include <set>
#include <vector>
#include <algorithm>
#include <iostream>
#include <iterator>
#include <map>
#include "TaintInliner.h"

#define TAINT_INFO2 std::cout << "[TAINT]: "

using namespace llvm;

namespace taint {

class RelValue {
public:
  Instruction *inst;
  Value *relVal;
 
  explicit RelValue(Instruction *_inst, 
                    Value *_val) : inst(_inst), 
                                   relVal(_val) {} 
};

class RelFlowSet {
public:
  std::vector<RelValue> sharedReadVec;
  std::vector<RelValue> sharedWriteVec;
  std::vector<RelValue> globalReadVec;
  std::vector<RelValue> globalWriteVec;

  RelFlowSet(); 

  ~RelFlowSet() {
    sharedReadVec.clear();
    sharedWriteVec.clear();
    globalReadVec.clear();
    globalWriteVec.clear();
  }

  bool empty() {
    return sharedReadVec.empty()
             && sharedWriteVec.empty()
               && globalReadVec.empty()
                 && globalWriteVec.empty();
  }
};

class CFGTaintSet {
public: 
  // This branch must be explored if set true
  // because this branch potentially will influence 
  // the race checking 
  bool explore;
  std::set<Instruction*> instSet;

  explicit CFGTaintSet(bool _explore, 
                       std::set<Instruction*> _instSet) : explore(_explore), 
                                                          instSet(_instSet) {}

  CFGTaintSet(const CFGTaintSet &taintSet) : explore(taintSet.explore), 
                                             instSet(taintSet.instSet) {}

  ~CFGTaintSet() {
    instSet.clear();
  } 
};

class CFGNode {
public:
  Instruction *inst;
  BasicBlock *postDom;
  bool isBrCond;
  bool causeIteration;
  unsigned outOfIteration;
  unsigned which; // which path is being explored   
  CFGNode *parent;
  bool allFinish;
  bool tainted;
  std::vector<CFGNode*> cfgNodes;
  std::vector<CFGTaintSet> cfgInstSet;
  std::vector<RelFlowSet> cfgFlowSet;

  CFGNode *successor;
  std::set<Instruction*> succInstSet;
  RelFlowSet succFlowSet;

  explicit CFGNode(Instruction *_inst, 
                   BasicBlock *_postDom, 
                   unsigned numSuccessors, 
                   bool _isBrCond) : inst(_inst), 
                                     postDom(_postDom), 
                                     isBrCond(_isBrCond) {
    which = 0;
    parent = NULL;
    causeIteration = false;
    allFinish = false;
    tainted = false;
    std::set<Instruction*> instSet;
    for (unsigned i = 0; i < numSuccessors; i++) {
      cfgNodes.push_back(NULL);
      cfgInstSet.push_back(CFGTaintSet(false, instSet));
      cfgFlowSet.push_back(RelFlowSet());
    }
    successor = NULL;
  }

  ~CFGNode() {
    cfgNodes.clear();
    cfgInstSet.clear();
    cfgFlowSet.clear();
  }
};

class VInstruction {
public:
  Instruction *inst;
};

class VFunction {
public:
  Function *func;
  VInstruction **insts;
  VInstruction **curInst;
  std::map<BasicBlock*, unsigned> basicBlockEntry;
  unsigned numInsts;

  explicit VFunction(Function *F);
  ~VFunction();
  void restoreCurInst();
  void setCurrentInst(Instruction *curInst);
  void setCurrentInstThroughEntry(unsigned entry);
  void dumpVFunctionInst();
 
  Instruction* getCurrentInst() {
    return (*curInst)->inst;
  }

  void stepInstruction() {
    curInst++;
  }
};

class TaintArgInfo {
public:
  std::string fName;
  Value *arg;
  bool taint;
  unsigned argNum;  
  std::set<Instruction*> taintInstList;
  std::set<Value*> taintValueSet;

  TaintArgInfo();
 
  explicit TaintArgInfo(std::string _fName, Value *_arg, 
                        bool _taint, unsigned _argNum) : 
                                       fName(_fName), 
                                       arg(_arg), 
                                       taint(_taint),
                                       argNum(_argNum) {}

  TaintArgInfo(const TaintArgInfo &info) : 
                                   fName(info.fName), 
                                   arg(info.arg), 
                                   taint(info.taint), 
                                   argNum(info.argNum), 
                                   taintInstList(info.taintInstList), 
                                   taintValueSet(info.taintValueSet) {}

  ~TaintArgInfo() {
    taintInstList.clear();
    taintValueSet.clear();
  }
};

class GlobalSharedTaint {
public:
  Value *gv;
  std::set<Instruction*> instSet;
  std::set<Value*> valueSet; 

  explicit GlobalSharedTaint(Value *_gv) : gv(_gv) {
    valueSet.insert(_gv);
  }

  ~GlobalSharedTaint() {
    instSet.clear();
    valueSet.clear();
  }
};

class CFGTree {
public: 
  std::set<Instruction*> preInstSet;
  RelFlowSet preFlowSet;

  CFGTree(); 
  ~CFGTree();
  void destroyCFGTree(CFGNode *node);
  CFGNode *getRootNode();
  CFGNode *getCurrentNode();
  CFGNode *getFlowCurrentNode();
  bool inIteration();
  void insertNodeIntoCFGTree(CFGNode *node);
  bool resetCurrentNodeInCFGTree(CFGNode *node, 
                                 Instruction *inst);
  void exploreCFGUnderIteration(Instruction *inst);
  bool isCFGTreeFullyExplored();
  unsigned getNodeNum() const {
    return nodeNum;
  }
  void insertCurInst(Instruction *inst, 
                     std::vector<TaintArgInfo> &argSet, 
                     AliasAnalysis &AA, 
                     std::vector<GlobalSharedTaint> &glSet,
                     std::vector<GlobalSharedTaint> &sharedSet);
  void setSyncthreadEncounter();
  bool exploreOneSideOfNode(CFGTaintSet &cfgTaintSet, 
                            RelFlowSet &relFlowSet, 
                            CFGNode *node, bool glAndsh);
  void exploreNodeCurrentBI(CFGNode *node, 
                            bool &singlePath, 
                            unsigned i, 
                            bool glAndsh); 
  void exploreNodeAcrossBI(CFGNode *node, 
                           bool &singlePath, 
                           unsigned i, 
                           bool glAndsh);
  void dumpNodeInstForDFSChecking(CFGNode *node, 
                                  unsigned i); 
  bool startDFSCheckingForCurrentBI(CFGNode *node); 
  void exploreCFGTreeToAnnotate(LLVMContext &glContext, 
                                Function *f, 
                                CFGNode *node);
  bool foundSameBrInstFromCFGTree(Instruction *inst, 
                                  CFGNode *node); 
  bool identifySuccessorRelation(BasicBlock *predBB, 
                                 BasicBlock *succBB); 
  bool enterIteration(Instruction *inst, 
                      CFGNode *current, 
                      std::set<BasicBlock*> &exploredBBSet, 
                      bool blockChange);
  void updateCurrentNode(Instruction *inst, 
                         bool &transfer);
  void setCFGNodeWithCauseIteration();
  void updateCurrentNodeAfterIteration();
  bool updateCFGTree(Instruction *inst, 
                     std::vector<TaintArgInfo> &taintArgSet, 
                     std::set<BasicBlock*> &exploredBBSet,
                     bool blockChange,
                     bool &finishIteration);
    
private:
  unsigned nodeNum;
  CFGNode *root;
  CFGNode *current;
  CFGNode *flowCurrent;
  CFGNode* iterateCFGNode;
  std::vector<TaintArgInfo> taintInfoSet;
  bool syncthreadEncounter;
};

class TaintAnalysisCUDA : public FunctionPass {
public:
  static char ID;
  std::map<std::string, bool> kernelSet;
  std::vector<VFunction*> functions;
  std::vector<GlobalSharedTaint> glSet;
  std::vector<GlobalSharedTaint> sharedSet;
  VFunction* curVFunc;
  CFGTree *cfgTree;
  bool enterIteration;

  std::set<BasicBlock*> exploredBBSet;
  std::set<CFGNode*> exploredCFGNodes;

  TaintAnalysisCUDA() : FunctionPass(ID) {}
  void dumpTaintArgInfo(TaintArgInfo &argInfo);
  CFGTree *getCFGTree() const {
    return cfgTree;
  }

  bool dumpAliasResult(Value *pointer, AliasAnalysis &AA, 
                       std::vector<Value*> &sharedSet, 
                       unsigned &num); 
  void encounterSyncthreadsBarrier(Instruction *inst);
  void insertCurInstToCFGTree(Instruction *inst, 
                              std::vector<TaintArgInfo> &taintArgSet, 
                              AliasAnalysis &AA);
  bool exploreCUDAKernel(Function *f, 
                         AliasAnalysis &AA);
  virtual bool runOnFunction(Function &F);

  bool doInitialization(Module &M);
  VFunction* getCurrentVFunction();

  void transferToBasicBlock(BasicBlock *dst);
  void handleBrInst(Instruction *inst, 
                    std::vector<TaintArgInfo> &argSet);
  void transferToIterationPostDom(Instruction *inst); 
  void transferToTheOtherSideCurrentNode();
  void handleSwitchInst(Instruction *inst,
                        std::vector<TaintArgInfo> &argSet);
  void handlePHINode(Instruction *inst, 
                     std::vector<TaintArgInfo> &argSet);
  void handleSelectInst(Instruction *inst, 
                        std::vector<TaintArgInfo> &argSet);
  void executeCall(Instruction *inst, 
                   Function *f,
                   std::vector<TaintArgInfo> &argSet, 
                   AliasAnalysis &AA);
  void executeCUDAArithOrConvIntrinsic(Instruction *inst, 
                                       std::string fName,
                                       std::vector<TaintArgInfo> &argSet);
  void executeCUDAAtomicIntrinsic(Instruction *inst, 
                                  std::string fName,
                                  std::vector<TaintArgInfo> &taintArgSet); 
  void executeCUDAIntrinsic(Instruction *inst, 
                            Function *f, 
                            std::vector<TaintArgInfo> &argSet);
  void handleArithmeticInst(Instruction *inst, 
                            std::vector<TaintArgInfo> &argSet);
  void handleCmpInst(Instruction *inst,
                     std::vector<TaintArgInfo> &argSet);
  void handleLoadInst(Instruction *inst,
                      std::vector<TaintArgInfo> &argSet, 
                      AliasAnalysis &AA);
  void handlePointerOperand(Instruction *inst, 
                            std::set<Instruction*> &instSet, 
                            std::set<Value*> &valueSet);
  void handleStoreInst(Instruction *inst, 
                       std::vector<TaintArgInfo> &argSet, 
                       AliasAnalysis &AA);
  void checkCFGTaintSetAffectRaceChecking(Value* val, 
                                          Instruction *inst, 
                                          bool sSink);
  void checkGEPIIndex(Instruction *inst, 
                      std::vector<TaintArgInfo> &argSet);
  void handleGetElementPtrInst(Instruction *inst, 
                               std::vector<TaintArgInfo> &argSet, 
                               AliasAnalysis &AA);
  void handleConversionInst(Instruction *inst,
                            std::vector<TaintArgInfo> &argSet);
  bool executeInstruction(Instruction *inst, 
                          std::vector<TaintArgInfo> &argSet,
                          AliasAnalysis &AA);

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<TaintInliner>();
    AU.addPreserved<TaintInliner>();
    AU.addRequired<AliasAnalysis>();
    AU.addPreserved<AliasAnalysis>();
  }
};

class ExecutorUtil {
public:
  static BasicBlock* findNearestCommonPostDominator(Instruction *inst, 
						    bool isCondBr); 
  static bool checkVarAliasToShared(Value *pointer, 
				    AliasAnalysis &AA, 
				    std::vector<GlobalSharedTaint> &glSet, 
				    std::vector<GlobalSharedTaint> &sharedSet, 
				    unsigned &num);
  static bool findValueFromTaintSet(Value *val, 
			    std::set<Instruction*> &taintInstList, 
			    std::set<Value*> &taintValueSet);
  static void insertGlobalSharedSet(Instruction *inst, 
				    Value *pointer, 
				    std::vector<GlobalSharedTaint> &set);
  static void dumpTaintInstList(std::set<Instruction*> &taintInstList);
  static void dumpTaintValueSet(std::set<Value*> &taintValueSet);
  static void checkLoadInst(Instruction *inst, 
                            std::vector<GlobalSharedTaint> &glSet, 
                            std::vector<GlobalSharedTaint> &sharedSet, 
                            AliasAnalysis &AA, 
                            RelFlowSet &flowSet); 
  static void checkStoreInst(Instruction *inst, 
                             std::vector<GlobalSharedTaint> &glSet, 
                             std::vector<GlobalSharedTaint> &sharedSet, 
                             AliasAnalysis &AA, 
                             RelFlowSet &flowSet); 
  static void checkAtomicInst(Instruction *inst, 
                              std::vector<GlobalSharedTaint> &glSet, 
                              std::vector<GlobalSharedTaint> &sharedSet, 
                              AliasAnalysis &AA, 
                              RelFlowSet &flowSet); 
};
}
