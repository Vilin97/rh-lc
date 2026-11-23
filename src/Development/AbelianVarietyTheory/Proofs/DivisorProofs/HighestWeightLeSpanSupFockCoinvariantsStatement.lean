module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Mathlib.Analysis.InnerProductSpace.l2Space
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Mathlib.Algebra.Order.Star.Rat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Definitions.Foundations.HarmonicAllOfCompact

section

@[expose] public section

noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]

end GlobalTheory.FockAlg.Model
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector

section

@[expose] public section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      AddMonoidAlgebra.coeff P α * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add (f := _), inner_add_right, h, h', MvPolynomial.coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, MvPolynomial.coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add (f := _), ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariants

section

@[expose] public section

noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.HoweR.MultOne

variable {P Q R S : ℕ}

theorem coinv_stable2 (x : ℂ) (Y : Mat R S) {v : Pol P Q R S} (hv : v ∈ coinv P Q R S x) :
    fockAct2 P Q R S Y v ∈ coinv P Q R S x := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩
    rw [map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem fockHarmonicsSecondMember_of_jointShape_highestWeight {x : ℚ} {μ' : Ix R S → ℚ} (hJ : JointShape P Q R S (fun _ => x) μ') {f : Pol P Q R S}
    (h2 : f ∈ harm2 P Q R S) (hc : f ∈ GlobalTheory.FockScalarType.charSub P Q R S x)
    (hw : f ∈ hwSub (fockAct2 P Q R S) μ') : f ∈ harm1 P Q R S := by
  by_cases h0 : f = 0
  · subst h0; intro Z _; simp [minusPart]
  obtain ⟨d, hd, hdf⟩ := isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)
  have hdeg := (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2
  intro Z hZ
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]
  by_cases hd2 : d < 2
  · exact dnOp_low _ d hd2 f hdf
  by_contra hne
  have h1 := isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf)
    (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))
  rw [hdeg, ← hd] at h1
  have e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
  rw [e] at h1
  linarith

end GlobalTheory.HoweR.MultOne

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.MultOne in
theorem hw_le_span_sup_coinv : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' →
    ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  intro P Q R S x μ' hJ
  set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
    Submodule.span ℂ (jointHarm P Q R S) with hL
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)
  refine ⟨v.1, fun g hg => ?_⟩
  set C := coinv P Q R S (x : ℂ) with hC
  let pr := C.mkQ
  have hker : ∀ w, pr w = 0 ↔ w ∈ C := fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f := by
    intro X f
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)
  have hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w') := by
    intro Y w w' h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (hker _).2 (coinv_stable2 _ Y ((hker _).1 h))
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]
  obtain ⟨h, hh, hprh⟩ := GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := GlobalTheory.HarmLift.lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw
      exacts [hs1 X hX w hw, hs2 Y hY w hw])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw
      · rw [hpr1, hw, smul_zero]
      · rw [hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hprh] at hcpr
  have hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x := fun X hX =>
    hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])
  have hcw : c ∈ hwSub (fockAct2 P Q R S) μ' := by
    have hg2 := hg
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      refine hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_
      rw [hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      rw [hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0
        (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]
  have hcJ : c ∈ jointHarm P Q R S := ⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩
  have hcL : c ∈ L := by
    by_cases h0 : c = 0
    · rw [h0]; exact L.zero_mem
    exact ⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩
  obtain ⟨t, ht⟩ := hv ⟨c, hcL⟩
  have hct : c = t • v.1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have hgc : g - c ∈ C := (hker _).1 (by rw [map_sub, hcpr, sub_self])
  rw [← sub_add_cancel g c, add_comm]
  exact Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc

end GlobalTheory.HoweR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariantsStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' → ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  first | exact @GlobalTheory.HoweR.hw_le_span_sup_coinv | exact GlobalTheory.HoweR.hw_le_span_sup_coinv | (intros; apply GlobalTheory.HoweR.hw_le_span_sup_coinv <;> assumption)
end
end
