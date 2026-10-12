import Qhl.Examples
import Qhl.Examples.SourceRuleIntegration
import Qhl.Examples.BoundedRUSTriple
import Qhl.Examples.RUSZeroBound
import Qhl.Logic.Source.Initialization
import Lean

/-! Check the explicitly registered source-rule integration exports. The exact endpoint
statements remain in their reviewed modules. Source soundness is an approved
semantic bridge; its internal implementation is not a consumer program proof.
-/
open Lean Elab Command

private def sourceRoots : List Name :=
  [``Qhl.SourceRuleIntegration.measuredDeriv,
   ``Qhl.SourceRuleIntegration.countLoopDeriv,
   ``Qhl.SourceRuleIntegration.countedProgramDeriv,
   ``Qhl.SourceRuleIntegration.selectedAllDeriv,
   ``Qhl.SourceRuleIntegration.selectedAttemptDeriv,
   ``Qhl.SourceRuleIntegration.convex1MeasurementDeriv,
   ``Qhl.SourceRuleIntegration.convex2SubprobDeriv,
   ``Qhl.BoundedRUS.boundedRusSourceDeriv,
   ``Qhl.BoundedRUS.boundedRusSuccessSourceDeriv,
   ``Qhl.BoundedRUS.successSourceDeriv_all,
   ``Qhl.BoundedRUS.boundedRusClassicalSourceDeriv,
   ``Qhl.BoundedRUS.boundedRusClassicalSuccessSourceDeriv,
   ``Qhl.SourceDerivTot.initFiniteBlock,
   ``Qhl.SourceDerivTot.initDynamicBlock]

-- Principal source results, including the retained and extended example specifications.
-- The quantitative RUS entry includes zero retries through its all-bound theorem.
private def principalSourceRoots : List (Name × Bool) :=
  [( ``Qhl.BellProgram.bellSourceDeriv, false),
   ( ``Qhl.ParallelHadamardSource.phDeriv, true),
   ( ``Qhl.ParallelHadamardSource.phDerivOn, true),
   ( ``Qhl.QFTSource.qftDeriv, true),
   ( ``Qhl.QFTClassicalSource.qftDeriv, true),
   ( ``Qhl.QFTClassicalSource.inputPreservedDeriv, true),
   ( ``Qhl.QFTClassicalSource.qftUniformDeriv, true),
   ( ``Qhl.QFTClassicalSource.qftAllInputDeriv, true),
   ( ``Qhl.QFTSource.qftUniformDeriv, true),
   ( ``Qhl.QFTArbitrarySource.qftDeriv, true),
   ( ``Qhl.QFTCompleteSource.qftAllInputDeriv, true),
   ( ``Qhl.InverseQFTSource.iqftRevDeriv, true),
   ( ``Qhl.InverseQFTClassicalSource.iqftRevDeriv, true),
   ( ``Qhl.QPESource.qpeDeriv, true),
   ( ``Qhl.QPEClassicalSource.qpeDeriv, true),
   ( ``Qhl.ClusterStateTriple.clusterSourceDeriv, true),
   ( ``Qhl.BoundedRUS.boundedRusSourceDeriv, true),
   ( ``Qhl.BoundedRUS.successSourceDeriv_all, true),
   ( ``Qhl.TrotterTFIMSource.tfimSourceDeriv, true),
   ( ``Qhl.TrotterTFIMSource.tfimSourceDerivExp, true),
   ( ``Qhl.TrotterTFIMSource.tfimSourceDerivApprox, true),
   ( ``Qhl.TrotterTFIMClassical.exactSourceDeriv, true),
   ( ``Qhl.TrotterTFIMClassical.identitySourceDeriv, true),
   ( ``Qhl.TrotterTFIMClassical.approxSourceDeriv, true),
   ( ``Qhl.BKTransform.bkSourceDeriv, true),
   ( ``Qhl.BKTransform.bkCoherentSourceDeriv, true),
   ( ``Qhl.HubbardLCU.Source.lcuDeriv, true),
   ( ``Qhl.HubbardLCUSuccess.Source.lcuSuccessDeriv, true),
   ( ``Qhl.HubbardLCUPredicate.lcuPredicateDeriv, true),
   ( ``Qhl.HubbardQSP.Source.qspDeriv, true),
   ( ``Qhl.HubbardQSPSuccess.Source.qspFidelityDeriv, true),
   ( ``Qhl.HubbardQSPPredicates.deriv, true),
   ( ``Qhl.HubbardQSPBK.deriv, true),
   ( ``Qhl.HubbardQSPBK.derivUnder, true),
   ( ``Qhl.HubbardQSPBK.stateCircuitDeriv, true),
   ( ``Qhl.HubbardQSPBK.stateDeriv, true),
   ( ``Qhl.HubbardLCUFullPredicate.deriv, true),
   ( ``Qhl.HubbardQSPFullPredicate.deriv, true),
   ( ``Qhl.HubbardQSPFullPredicate.bkDeriv, true),
   ( ``Qhl.HubbardQSPSpectral.deriv_of_norm_lt, true)]

private def reusedSourceRoots : List Name :=
  [``Qhl.ParallelHadamardSource.phDerivOnWith,
   ``Qhl.InverseQFTClassicalSource.iqftProdDeriv,
   ``Qhl.InverseQFTPlacedSource.Literal.iqftProdDeriv,
   ``Qhl.InverseQFTPlacedSource.Stored.iqftRevDeriv,
   ``Qhl.QFTArbitraryClassicalSource.qftDeriv,
   ``Qhl.TrotterTFIMSource.tfimSourceDerivApprox_of_norm,
   ``Qhl.TrotterTFIMSource.tfimSourceDerivApprox_of_coefficients]

private def resultHead : Expr → Option Name
  | .forallE _ _ body _ => resultHead body
  | type => type.getAppFn.constName?

private partial def dependencies (env : Environment) (todo : List Name)
    (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then dependencies env ns seen
    else
      let seen := seen.insert n
      let value := if n == ``Qhl.SourceDerivTot.sound || n == ``Qhl.SourceDerivPar.sound
        then none else
        match env.find? n with
        | some (.thmInfo v) => some v.value
        | some (.defnInfo v) => some v.value
        | some (.opaqueInfo v) => some v.value
        | _ => none
      let next := match value with
        | some v => v.getUsedConstants.toList
        | none => []
      dependencies env (next ++ ns) seen

run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``Qhl.SourceDerivTot.measureSelected, ``Qhl.SourceDerivPar.measureSelected] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "{n}: selected measurement must be a derived theorem, not a constructor"
  for n in (sourceRoots ++ principalSourceRoots.map Prod.fst ++ reusedSourceRoots).eraseDups do
    let some info := env.find? n | throwError "Missing source export {n}"
    unless resultHead info.type == some ``Qhl.SourceDerivTot do
      throwError "{n}: result is not SourceDerivTot"
    let deps := dependencies env [n] {}
    for d in deps.toList do
      match env.find? d with
      | some (.ctorInfo c) =>
        if c.induct == ``Qhl.DerivTot || c.induct == ``Qhl.DerivPar then
          throwError "{n}: retained backend constructor dependency {d}"
      | _ => pure ()
    if n == ``Qhl.BoundedRUS.boundedRusSourceDeriv ||
        n == ``Qhl.BoundedRUS.boundedRusSuccessSourceDeriv ||
        n == ``Qhl.BoundedRUS.boundedRusClassicalSourceDeriv ||
        n == ``Qhl.BoundedRUS.boundedRusClassicalSuccessSourceDeriv then
      for required in [``Qhl.SourceDerivTot.measureAll, ``Qhl.SourceDerivTot.mask,
          ``Qhl.SourceDerivTot.whileLoop] do
        unless deps.contains required do
          throwError "{n}: missing source-rule dependency {required}"
    if [``Qhl.SourceRuleIntegration.measuredDeriv,
        ``Qhl.SourceRuleIntegration.selectedAllDeriv,
        ``Qhl.SourceRuleIntegration.selectedAttemptDeriv].contains n then
      for required in [``Qhl.SourceDerivTot.measureAll, ``Qhl.SourceDerivTot.mask] do
        unless deps.contains required do
          throwError "{n}: missing measurement/mask constructor {required}"
    if principalSourceRoots.contains (n, true) &&
        !deps.contains ``Qhl.SourceDerivTot.whileLoop then
      throwError "{n}: source total-loop dependency missing"
    let required :=
      if n == ``Qhl.SourceRuleIntegration.convex1MeasurementDeriv then
        [``Qhl.SourceDerivTot.convex1, ``Qhl.SourceDerivTot.measureAll,
         ``Qhl.SourceDerivTot.mask]
      else if n == ``Qhl.SourceRuleIntegration.convex2SubprobDeriv then
        [``Qhl.SourceDerivTot.convex2]
      else if n == ``Qhl.BoundedRUS.successSourceDeriv_all then
        [``Qhl.SourceDerivTot.convex2, ``Qhl.SourceDerivTot.whileLoop]
      else if n == ``Qhl.SourceDerivTot.initDynamicBlock then
        [``Qhl.SourceDerivTot.initProg, ``Qhl.SourceDerivTot.cond, ``Qhl.SourceDerivTot.seq]
      else []
    for d in required do
      unless deps.contains d do
        throwError "{n}: missing required source constructor {d}"
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "{n}: unexpected axioms {axioms}"
    logInfo m!"PASS {n}: source derivation; no backend constructor dependency; standard axioms"

  let qft := dependencies env [``Qhl.QFTCompleteSource.qftAllInputDeriv] {}
  for n in [``Qhl.QFTSource.qftDeriv, ``Qhl.QFTSource.qftUniformDeriv,
      ``Qhl.QFTArbitrarySource.qftDeriv] do
    unless qft.contains n do throwError "Missing source QFT phase input {n}"
  for n in [``Qhl.QFTTriple.qftCirOp_eq_qftOp, ``Qhl.QFTTriple.qftCirOp_apply_eq,
      ``Qhl.QFTTriple.qftCirOp_deltav, ``Qhl.QFTTriple.qftCirOp_prodV_qbit,
      ``Qhl.QFTTriple.qftIterOp_prodV, ``Qhl.QFTTriple.qftStageOp_prodV,
      ``Qhl.QFTTriple.qftSubOp_prodV, ``Qhl.QFTTriple.revCircOp_prodV_fam] do
    if qft.contains n then throwError "Old composite Fourier correctness dependency {n}"
  logInfo "PASS QFT phase recovery uses source basis, uniform, and circuit-output proofs"
  for (root, ph, iqft) in
      [(``Qhl.QPESource.qpeDeriv, ``Qhl.ParallelHadamardSource.phDerivOn,
        ``Qhl.InverseQFTPlacedSource.Literal.iqftProdDeriv),
       (``Qhl.QPEClassicalSource.qpeDeriv, ``Qhl.ParallelHadamardSource.phDerivOnWith,
        ``Qhl.InverseQFTPlacedSource.Stored.iqftRevDeriv)] do
    let deps := dependencies env [root] {}
    for n in [ph, iqft] do
      unless deps.contains n do throwError "{root}: missing source subroutine {n}"
  logInfo "PASS both QPE proofs reuse source Hadamard and placed inverse-QFT proofs"
  for (root, qsp) in
      [(``Qhl.HubbardQSPBK.deriv, ``Qhl.HubbardQSPPredicates.circuit),
       (``Qhl.HubbardQSPBK.stateCircuitDeriv, ``Qhl.HubbardQSP.Source.qspDeriv),
       (``Qhl.HubbardQSPBK.stateDeriv, ``Qhl.HubbardQSP.Source.qspDeriv)] do
    let deps := dependencies env [root] {}
    for n in [``Qhl.BKTransformWp.sourceDeriv, qsp] do
      unless deps.contains n do throwError "{root}: missing source BK/QSP subroutine {n}"
  logInfo "PASS BK-prefixed QSP proofs reuse the literal source BK and QSP derivations"
  let backend := dependencies env [``Qhl.BellProgram.bellStateDeriv] {}
  unless backend.contains ``Qhl.DerivTot.unitary do
    throwError "negative control failed: backend constructor not detected"
  let legacy := dependencies env [``Qhl.DerivTot.countedWhile] {}
  unless legacy.contains ``Qhl.DerivTot.whileLoop do
    throwError "negative control failed: legacy loop not detected"
  logInfo "PASS backend-constructor and legacy-loop negative controls"
