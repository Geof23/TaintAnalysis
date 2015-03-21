#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/IR/DataLayout.h"

#include <iostream>

using namespace llvm;

namespace taint {

class TaintInliner : public Inliner {
  //InlineCostAnalyzer CA;
public:
  TaintInliner() : Inliner(ID) {
    initializeSimpleInlinerPass(*PassRegistry::getPassRegistry());
  }
  TaintInliner(int Threshold) : Inliner(ID, Threshold,
                                        /*InsertLifetime*/true) {
    initializeSimpleInlinerPass(*PassRegistry::getPassRegistry());
  }
  static char ID; // Pass identification, replacement for typeid
  InlineCost getInlineCost(CallSite CS) {
    Function *Callee = CS.getCalledFunction();
    // We assume indirect calls aren't calling an always-inline function.
    if (!Callee) return InlineCost::getNever();

    // We can't inline calls to external functions.
    // FIXME: We shouldn't even get here.
    if (Callee->isDeclaration()) 
      return InlineCost::getNever();

    if (Callee->hasFnAttribute(Attribute::AttrKind::NoInline))
      return InlineCost::getNever();

    // Otherwise, force inlining.
    return InlineCost::getAlways();
  }
  using Pass::doInitialization;
  virtual bool doInitialization(CallGraph &CG);
};

}
