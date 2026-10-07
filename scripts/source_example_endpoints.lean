import Qhl.Examples
import Lean

/-! Compare source-derived semantic exports with the original principal signatures.
Only the final DerivTot is replaced by validTot; program, assertions, quantifiers,
and hypotheses must still be definitionally equal. CQ decomposition is additionally
reviewed in the source proof statements, since equal effects do not imply equal
classical conditions.
-/
open Lean Meta Elab Command

private def endpoints : List (Name × Name) :=
  [(``Qhl.BellProgram.bellStateDeriv, ``Qhl.BellProgram.bellSourceValid),
   (``Qhl.ParallelHadamardTriple.phDeriv, ``Qhl.ParallelHadamardSource.phValid),
   (``Qhl.ParallelHadamardTriple.phDerivOn, ``Qhl.ParallelHadamardSource.phValidOn),
   (``Qhl.QFTTriple.qftDeriv, ``Qhl.QFTSource.qftValid),
   (``Qhl.QFTClassicalTriple.qftDeriv, ``Qhl.QFTClassicalSource.qftValid),
   (``Qhl.QFTClassicalTriple.inputPreservedDeriv, ``Qhl.QFTClassicalSource.inputPreservedValid),
   (``Qhl.QFTClassicalTriple.qftUniformDeriv, ``Qhl.QFTClassicalSource.qftUniformValid),
   (``Qhl.QFTClassicalTriple.qftAllInputDeriv, ``Qhl.QFTClassicalSource.qftAllInputValid),
   (``Qhl.QFTUniform.qftUniformDeriv, ``Qhl.QFTSource.qftUniformValid),
   (``Qhl.QFTArbitrary.qftDeriv, ``Qhl.QFTArbitrarySource.qftValid),
   (``Qhl.QFTComplete.qftAllInputDeriv, ``Qhl.QFTCompleteSource.qftAllInputValid),
   (``Qhl.InverseQFTTriple.iqftRevDeriv, ``Qhl.InverseQFTSource.iqftRevValid),
   (``Qhl.InverseQFTClassicalTriple.iqftRevDeriv, ``Qhl.InverseQFTClassicalSource.iqftRevValid),
   (``Qhl.QPETriple.qpeDeriv, ``Qhl.QPESource.qpeValid),
   (``Qhl.QPEClassicalTriple.qpeDeriv, ``Qhl.QPEClassicalSource.qpeValid),
   (``Qhl.ClusterStateTriple.clusterDeriv, ``Qhl.ClusterStateTriple.clusterSourceValid),
   (``Qhl.BoundedRUS.boundedRusDeriv, ``Qhl.BoundedRUS.boundedRusSourceValid),
   (``Qhl.BoundedRUS.boundedRusSuccessDeriv, ``Qhl.BoundedRUS.boundedRusSuccessSourceValid_all),
   (``Qhl.TrotterTFIM.tfimDeriv, ``Qhl.TrotterTFIMSource.tfimSourceValid),
   (``Qhl.TrotterTFIM.tfimDerivExp, ``Qhl.TrotterTFIMSource.tfimSourceValidExp),
   (``Qhl.TrotterTFIM.tfimDerivApprox, ``Qhl.TrotterTFIMSource.tfimSourceValidApprox),
   (``Qhl.TrotterTFIMClassical.exactDeriv, ``Qhl.TrotterTFIMClassical.exactSourceValid),
   (``Qhl.TrotterTFIMClassical.identityDeriv, ``Qhl.TrotterTFIMClassical.identitySourceValid),
   (``Qhl.TrotterTFIMClassical.approxDeriv, ``Qhl.TrotterTFIMClassical.approxSourceValid),
   (``Qhl.BKTransform.bkDeriv, ``Qhl.BKTransform.bkSourceValid),
   (``Qhl.HubbardLCU.lcuDeriv, ``Qhl.HubbardLCU.Source.lcuValid),
   (``Qhl.HubbardLCUSuccess.lcuSuccessDeriv, ``Qhl.HubbardLCUSuccess.Source.lcuSuccessValid),
   (``Qhl.HubbardQSP.qspDeriv, ``Qhl.HubbardQSP.Source.qspValid),
   (``Qhl.HubbardQSPSuccess.qspFidelityDeriv, ``Qhl.HubbardQSPSuccess.Source.qspFidelityValid)]

private partial def semanticType : Expr → MetaM Expr
  | .forallE n d b bi => return .forallE n d (← semanticType b) bi
  | e =>
    match e.getAppFn with
    | .const n us => do
      unless n == ``Qhl.DerivTot do throwError "Expected original DerivTot result"
      return mkAppN (.const ``Qhl.validTot us) e.getAppArgs
    | _ => throwError "Expected original derivation type"

run_cmd do
  liftTermElabM do
    for (old, current) in endpoints do
      let expected ← semanticType (← inferType (← mkConstWithFreshMVarLevels old))
      let actual ← inferType (← mkConstWithFreshMVarLevels current)
      unless ← isDefEq expected actual do
        throwError "Endpoint signature mismatch: {old} / {current}\nExpected: {expected}\nActual: {actual}"
      logInfo m!"PASS exact original program/specification signature: {current}"
