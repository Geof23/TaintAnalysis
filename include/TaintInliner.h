#include "llvm/CallingConv.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Type.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/DataLayout.h"

#include <iostream>

using namespace llvm;

namespace taint {

class TaintInliner : public Inliner {
  InlineCostAnalyzer CA;
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

    if (Callee->getFnAttributes().hasAttribute(Attributes::NoInline))
      return InlineCost::getNever();

    // Otherwise, force inlining.
    return InlineCost::getAlways();
  }
  virtual bool doInitialization(CallGraph &CG);
};

}
