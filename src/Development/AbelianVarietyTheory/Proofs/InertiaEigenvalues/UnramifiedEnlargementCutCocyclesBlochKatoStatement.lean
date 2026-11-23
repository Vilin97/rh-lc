module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionConductorTwistedCharacterAdmissi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionTwistedWeilCoefficientsAdmissibl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocyclesLocallyConstantKilledByUniformiserPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModIntStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgroStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocalStatement

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | exact GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | (intros; apply GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocycStatement

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.liftC_main | exact GlobalTheory.UseLoc.Cases.liftC_main | (intros; apply GlobalTheory.UseLoc.Cases.liftC_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundaryStatement

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  first | exact @GlobalTheory.UseLoc.Cases.readW_main | exact GlobalTheory.UseLoc.Cases.readW_main | (intros; apply GlobalTheory.UseLoc.Cases.readW_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedChar

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem chiOC_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : chiOC C 1 = 1 := by
  ext g; simp [chiOC]

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  rw [chiT, mul_inv_cancel, chiOC_one, one_mul]

theorem repV_eq_inv_smul_twist : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  intro D i w hw C k N θ g
  rw [chiT_one]
  have h : repV C (twistM N θ) g = (algebraMap (↥(OL C.LL)) (↥C.LL.1) (θ g : ↥(OL C.LL))) • repV C N g := by
    simp only [repV, matRep, mapM, twistM]
    simp [RingHom.mapMatrix_apply, Matrix.map_smul', Matrix.toLinAlgEquiv'_apply]
    rw [show ((θ g : ↥(OL C.LL)) • N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)
        = (algebraMap ↥(OL C.LL) ↥C.LL.1 (θ g : ↥(OL C.LL))) • (N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) from by
          ext a b; simp [Matrix.map_apply], map_smul]
    rfl
  rw [h, smul_smul]
  simp [tableLineDegreeTwo.charL]

end GlobalTheory.UseLoc.Cases
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedCharStatement

section

@[expose] public section



open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

theorem _root_.GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  first | exact @GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | exact GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | (intros; apply GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UseLoc.Cases

set_option maxHeartbeats 8000000 in
theorem partW : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (WpO D.nd i ρ π) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle D i w hw C lam hlam (locOC C (WpO D.nd i ρ π)) θ a
    (fun g => liftQ C.le D.R.r (z g)) hZ hk
  have hz'' : ∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g) := hz'
  have hadm := GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont z hz a z' hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).1 (repV C (locOC C (WpO D.nd i ρ π)))
    (latC C (locOC C (WpO D.nd i ρ π))) (GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul D i w hw C (locOC C (WpO D.nd i ρ π)) θ) rfl z' hcoc).1 hadm
  have hr := GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary D i w hw C lam (locOC C (WpO D.nd i ρ π)) θ a z' hin
  have e : (fun g => liftQ C.le D.R.r (z g)) = fun g => iotaW ↥C.LL.1 lam a D.R.r (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partC : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont c hc z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i c) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ c a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : c ∈ Finset.Icc 1 D.R.t :=
    Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hc).1; omega, (Finset.mem_Icc.1 hc).2⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont c hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.1 c hc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary D i w hw C lam θ c a z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partU : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i 1) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ 1 a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : 1 ∈ Finset.Icc 1 D.R.t := Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont 1 hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.2 (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup D i w hw C lam θ a _ z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont
  exact ⟨partW D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partC D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partU D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont⟩

end GlobalTheory.UseLoc.Cases

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKatoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  first | exact @GlobalTheory.UseLoc.Cases.main | exact GlobalTheory.UseLoc.Cases.main | (intros; apply GlobalTheory.UseLoc.Cases.main <;> assumption)
end
end
