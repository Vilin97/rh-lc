module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvectorStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedVectorCoefficientLeftInvariantLevelGroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamiliesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdateStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSumStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLaws

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

namespace GlobalTheory.RawLift.Covol

theorem exists_isCovolOne_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i
  exact GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)

end GlobalTheory.RawLift.Covol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLawsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 := by
  first | exact @GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | exact GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | (intros; apply GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lx_eq_of_rep_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : LX R i v}
    (h : (rep x)⁻¹ * rep y ∈ levW R i) : x = y := by
  have : (Quotient.mk _ (Quotient.out x) : LX R i v) = Quotient.mk _ (Quotient.out y) := by
    apply Quotient.sound
    change ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i))) _ _
    rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
    exact h
  exact (Quotient.out_eq x).symm.trans (this.trans (Quotient.out_eq y))

theorem rep_notMem_levW {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x : LX R i v}
    (hx : x ≠ lx0 R i v) : rep x ∉ levW R i := fun h =>
  hx (lx_eq_of_rep_rel ((levW R i).mul_mem ((levW R i).inv_mem h) (trivial_level_coset_representative_mem_level R i v)))

theorem rep_suppF {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    SuppF (Wc D i) (fid D v) (rep x) := (Quotient.out x).2.2

theorem eq_one_of_suppF_zero {V : HSp D} {g : GA D V} (h : SuppF V 0 g) : g = 1 := by
  have e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V 1 := by
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := rfl
    rw [h1, ← sub_eq_zero]
    ext a b
    have := h a b
    simpa [eq_comm] using this
  exact Subtype.ext (Units.ext e)

end

theorem acoef_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hb⟩ := hLS μ 𝓕 hμ
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · refine Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => ?_) hs.abs
    exact max_le (le_abs_self _) (abs_nonneg _)
  · intro v C hC
    by_cases hex : ∃ f, IsFinIdem D v f
    · have hf : IsFinIdem D v (fid D v) := by
        unfold fid
        rw [dite_eq_left hex]
        exact hex.choose_spec
      have hinj : Function.Injective (rep : LX R i v → GA D (Wc D i)) := fun x y h =>
        lx_eq_of_rep_rel (by rw [h, inv_mul_cancel]; exact (levW R i).one_mem)
      have := hb v _ hf (C.image rep) ?_ ?_
      · rw [Finset.sum_image (fun x _ y _ h => hinj h)] at this
        exact this.trans (le_max_left _ _)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨rep_suppF x, rep_notMem_levW fun e => hC (e ▸ hx)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hg'
        rw [lx_eq_of_rep_rel h]
    · have hf : fid D v = 0 := by
        unfold fid
        rw [dite_eq_right hex]
      have hC0 : C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have h1 : rep x = 1 := eq_one_of_suppF_zero (hf ▸ rep_suppF x)
        exact rep_notMem_levW (fun e => hC (e ▸ hx)) (h1 ▸ (levW R i).one_mem)
      rw [hC0, Finset.sum_empty]
      exact le_max_right _ _

end GlobalTheory.RawLift.Eu

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  first | exact @GlobalTheory.RawLift.Eu.acoef_small | exact GlobalTheory.RawLift.Eu.acoef_small | (intros; apply GlobalTheory.RawLift.Eu.acoef_small <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem scalar_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : Submodule ℂ H)
    (Wop : H →L[ℂ] H) (hinj : Function.Injective Wop) (heig : ∀ y ∈ P, ∃ z : ℂ, Wop y = z • y) :
    ∃ l : ℂ, l ≠ 0 ∧ ∀ x ∈ P, Wop x = l • x := by
  by_cases h : ∃ x0 ∈ P, x0 ≠ 0
  · obtain ⟨x0, hx0, hne⟩ := h
    obtain ⟨l, hl⟩ := heig x0 hx0
    refine ⟨l, ?_, ?_⟩
    · rintro rfl
      apply hne
      apply hinj
      rw [hl, zero_smul, map_zero]
    · intro x hx
      obtain ⟨lx, hlx⟩ := heig x hx
      obtain ⟨m, hm⟩ := heig (x + x0) (P.add_mem hx hx0)
      rw [map_add (f := _), hlx, hl, smul_add] at hm
      by_cases hmx : m = lx
      · subst hmx
        have : (l - m) • x0 = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel hm)
        rcases smul_eq_zero.1 this with h1 | h1
        · rw [hlx, sub_eq_zero.1 h1]
        · exact absurd h1 hne
      · have hx' : x = ((l - m) / (m - lx)) • x0 := by
          have e1 : (m - lx) • x = (l - m) • x0 := by
            rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
            rw [← hm]; abel
          have hne' : m - lx ≠ 0 := sub_ne_zero.2 hmx
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hne', one_smul]
        rw [hx', map_smul, hl, smul_comm]
  · push_neg at h
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    rw [h x hx, map_zero, smul_zero]


theorem innerNe_main {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hL : Laws R F) (i : Fin D.R.m) (t : T) (hFS : FinSum R i t) (hFM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) (hLS : LocSmall R i t) (hBS : BadSupp R i t) (hLP : LevProd R i) (hTL : TransLaws R i) :
    InnerNe R i t ∅ := by
  intro th hth c
  have hcov := @GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws D G _ _ Pl0 T A Ks _ _ _ R F hL i
  obtain ⟨μ, 𝓕, hμ⟩ := hcov
  have hleft := @GlobalTheory.T.fixedVectorCoefficient_left_invariant_levelGroup D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF μ 𝓕 hμ
  have hfa := @GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies D G _ _ Pl0 T A Ks _ _ _ R i t hLP hTL hFM hLF hVN hFS th hth μ 𝓕 hμ
  have hsm := @GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨a, ha, hfam⟩ := hfa
  obtain ⟨s, hs, hs1, hsC⟩ := hsm
  have hconv := @GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft
  have hupd := @GlobalTheory.T.rightTranslateOperator_familyProd_update D G _ _ Pl0 T A Ks _ _ _ R i hTL
  have heig := @GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace D G _ _ Pl0 T A Ks _ _ _ R F hL i t hBS hLF hLS hLP hTL μ 𝓕 hμ hleft c
  have hUpd : ∀ v (f : ∀ v, Eu.LX R i v), {w | f w ≠ Eu.lx0 R i w}.Finite → f v = Eu.lx0 R i v →
      HasSum (fun x => Eu.acoef R i t μ 𝓕 v x • Eu.Bfam R i (Function.update f v x))
        (Eu.Bfam R i f * Eu.Zop R i t μ 𝓕 v) := by
    intro v f hf hv
    obtain ⟨hG, hB⟩ := hupd f hf v hv
    have := hconv v _ hG
    unfold Eu.Bfam
    simp only [hB]
    exact this
  have hEu := GlobalTheory.T.eulerOperator_injective_eigenvector (HeightOneSpectrum (𝓞 D.host.F)) (Eu.LX R i) (Eu.lx0 R i)
    (R.HW i (sg0 D A)).H (Eu.acoef R i t μ 𝓕) s (Eu.Bfam R i) (Eu.Zop R i t μ 𝓕)
    (local_coefficient_trivial_level_coset hLF hVN hμ) hs hs1 hsC (fun f => bop_norm R i _)
    (by unfold Eu.Bfam; rw [localCosetFamilyRepresentativeProd_trivial_eq_one]; exact bop_one hTL) hUpd
  obtain ⟨Wop, hW, hinj, hWe⟩ := hEu
  have hip : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a : ℂ) * ⟪x, Wop y⟫_ℂ := by
    intro x y
    let φ : ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ _ y)
    have h1 := (hW.mapL φ).mul_left (a : ℂ)
    have h2 := hfam x y
    refine h2.unique ?_
    simpa [φ, inner_smul_right] using h1
  have hE : ∀ y ∈ part R i ∅ c, ∃ z : ℂ, Wop y = z • y := by
    intro y hy
    have hz := fun v => heig y hy v
    choose z hz using hz
    exact ⟨_, hWe y z hz⟩
  have hsc := scalar_of_eigen (part R i ∅ c) Wop hinj hE
  obtain ⟨l, hl, hlx⟩ := hsc
  refine ⟨(a : ℂ) * (starRingEnd ℂ) l, mul_ne_zero (by exact_mod_cast ha.ne') (by simpa using hl), ?_⟩
  intro x hx y
  rw [← inner_conj_symm, hip y x, hlx x hx, inner_smul_right, map_mul, map_mul, Complex.conj_ofReal,
    inner_conj_symm]
  ring

end GlobalTheory.RawLift.Eu

namespace GlobalTheory.RawLift

theorem innerNe_spherical : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → BadSupp R i t → LevProd R i → TransLaws R i → InnerNe R i t ∅ :=
  fun _ _ _ _ _ _ _ _ _ _ _ R F hL _ i t hFS hFM hLF hVN hLS hBS hLP hTL =>
    Eu.innerNe_main R F hL i t hFS hFM hLF hVN hLS hBS hLP hTL

end GlobalTheory.RawLift

end
end
end
