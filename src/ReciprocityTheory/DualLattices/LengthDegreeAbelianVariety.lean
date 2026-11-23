module

public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.ColengthSqMulLeProd
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
public import ReciprocityTheory.DualLattices.IsLocalOfIntegers
public import ReciprocityTheory.DualLattices.LenEx
public import ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
public import ReciprocityTheory.DualLattices.BasechangeProjectorIdempotentAction
public import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
public import ReciprocityTheory.DualLattices.RestrictHopfOrderLength
public import ReciprocityTheory.DualLattices.SmithNormalFormStatement
public import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.SumValCoord
public import ReciprocityTheory.DualLattices.VDetEqOneOfIntegral
public import Mathlib.RingTheory.LocalRing.Module

-- Source module: ReciprocityTheory.DualLattices.IdemGen

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

theorem idemGen : IdemGenStatement := by
  rintro R _ g d P hP ⟨e⟩

  let L : (Fin g → R) →ₗ[R] (Fin d → R) := e.toLinearMap ∘ₗ (mulVecLin P).rangeRestrict
  let T : (Fin d → R) →ₗ[R] (Fin g → R) :=
    (LinearMap.range (mulVecLin P)).subtype ∘ₗ e.symm.toLinearMap
  obtain ⟨M, hLM⟩ : ∃ M : Matrix (Fin d) (Fin g) R, Matrix.toLin' M = L :=
    ⟨_, Matrix.toLin'_toMatrix' L⟩
  obtain ⟨N, hTN⟩ : ∃ N : Matrix (Fin g) (Fin d) R, Matrix.toLin' N = T :=
    ⟨_, Matrix.toLin'_toMatrix' T⟩

  have hPNM : P = N * M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM, hTN]
    refine LinearMap.ext fun x => ?_
    simp [L, T, Matrix.toLin'_apply]

  have hMP : M * P = M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, L, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hP]

  have hrow : ∀ i, Pᵀ *ᵥ M i = M i := by
    intro i
    funext j
    have h := congrFun (congrFun hMP i) j
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine ⟨fun i => ⟨M i, LinearMap.mem_range.mpr ⟨M i, by rw [Matrix.mulVecLin_apply]; exact hrow i⟩⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw

  have key : mulVecLin Pᵀ v = ∑ i, (Nᵀ *ᵥ v) i • M i := by
    rw [Matrix.mulVecLin_apply, hPNM, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨fun i => (Nᵀ *ᵥ v) i, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact key.symm

end ReciprocityTheory.PGsh.Up
end
end
end

-- Source module: ReciprocityTheory.DualLattices.KilledGen

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.PGsh.Up

theorem killedGen : KilledGenStatement := by
  intro C _ v R _ _ hv M _ _ x d c hx hy hc
  obtain ⟨y, hy⟩ := hy
  have h := prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end ReciprocityTheory.PGsh.Up
end
end
end

-- Source module: ReciprocityTheory.DualLattices.WdetDegreeOfSmithRestrict

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

lemma idem_basis {S : Type} [CommRing S] [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι S) (hP : P * P = P) : ∃ (r : ℕ) (Bw : Matrix ι (Fin r) S),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin P) ∧
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ := by
  classical
  let f : (ι → S) →ₗ[S] (ι → S) := Matrix.mulVecLin P
  have hidem : ∀ x, f (f x) = f x := fun x => by
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  let M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    simp [hidem]
  haveI : Module.Projective S M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis S M
  have hBw : Matrix.mulVecLin (Matrix.of fun i j => (b j : ι → S) i) =
      M.subtype ∘ₗ b.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank S M, Matrix.of fun i j => (b j : ι → S) i, ?_, ?_⟩
  · rw [hBw, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · rw [hBw, LinearMap.ker_eq_bot]
    exact M.injective_subtype.comp b.equivFun.symm.injective

theorem wdetDegree_of_smith_restrict (hS : EigenQuotientSmithStatement) (hR : RestrictedHopfOrderStatement) (hC : RestrictedHopfOrderApproximationStatement) :
    WdetDegStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw d X hd hX
  classical
  have hv := hSet.integers
  have hidem : e w * e w = e w := by rw [horth, if_pos rfl]
  have hρidem : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, hidem]
  obtain ⟨r, Bw, hrange, hker⟩ := idem_basis (H.ρ (e w)) hρidem
  obtain ⟨Λ, dj, hΛ, hdjspan, hdjv, hXeq⟩ :=
    hS p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX
  obtain ⟨AW, hAWc, hOm⟩ := hR p g C v R O σ cp hSet H (e w) hidem r Bw hrange hker d hd
  have hcl := fun j => hC p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker (Λ j) (dj j) (hdjspan j) (hdjv j)
  choose x hxmem hxapp using hcl
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h1 := hSet.cp_val
    rw [h0, zero_pow (by omega)] at h1
    exact hSet.p_ne h1.symm
  have hdj0 : ∀ j, algebraMap R C (dj j) ≠ 0 := fun j h0 => by
    have h1 := hdjv j
    rw [h0, map_zero, le_zero_iff] at h1
    exact hcp0 h1
  have hpC : v (p : C) < 1 := by
    have h1 := hSet.p_lt
    rwa [map_natCast] at h1
  set u : Fin r → (Fin r → ZMod p) → C := fun j y => (algebraMap R C (dj j))⁻¹ * x j y with hudef
  have hred : ∀ y : Fin r → ZMod p, (fun i => PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p])) = y := by
    intro y
    funext i
    simp
  have hU2 : ∀ j y, v (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) < 1 := by
    intro j y
    have h1 := hxapp j (fun i => (((y i).val : ℕ) : ℤ_[p]))
    rw [hred y] at h1
    simp only [map_natCast] at h1
    have e1 : u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R)) =
        (x j y - algebraMap R C (dj j * ∑ i, Λ j i * ((y i).val : R))) / algebraMap R C (dj j) := by
      simp only [hudef, map_mul]
      field_simp [hdj0 j]
    rw [e1, map_div₀]
    exact (div_lt_one (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdj0 j)))).2 h1
  have hU1 : ∀ j y, v (u j y) ≤ 1 := by
    intro j y
    have e1 : u j y = (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) +
        algebraMap R C (∑ i, Λ j i * ((y i).val : R)) := by ring
    rw [e1]
    exact (Valuation.map_add v _ _).trans (max_le (hU2 j y).le (hv.map_le_one _))
  have h5 := (u5 p C v R hv hpC (Fin r) Λ u hΛ hU1 hU2).2 (fun j => algebraMap R C (dj j))
  have hxu : ∀ j y, algebraMap R C (dj j) * u j y = x j y := fun j y => by
    simp only [hudef]
    rw [mul_inv_cancel_left₀ (hdj0 j)]
  simp only [hxu] at h5
  have hxW : ∀ j, x j ∈ AW.carrier := fun j => hAWc ▸ hxmem j
  have hpow : ∀ (f : (Fin r → ZMod p) → C), f ∈ AW.carrier → ∀ k : ℕ, f ^ k ∈ AW.carrier := by
    intro f hf k
    induction k with
    | zero => rw [pow_zero]; exact AW.one_mem
    | succ k ih => rw [pow_succ]; exact AW.mul_mem _ _ ih hf
  have hmon : ∀ α : Fin r → ZMod p, (fun y => ∏ j, x j y ^ (α j).val) ∈ AW.carrier := by
    intro α
    have key : ∀ s : Finset (Fin r), (∏ j ∈ s, x j ^ (α j).val) ∈ AW.carrier := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact AW.one_mem
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact AW.mul_mem _ _ (hpow _ (hxW a) _) ih
    convert key Finset.univ using 1
    funext y
    simp [Finset.prod_apply]
  obtain ⟨B, hBu, hBc⟩ := AW.lat
  have hcol : ∀ α : Fin r → ZMod p, ∃ c : (Fin r → ZMod p) → R,
      ∑ j', c j' • (fun y => B y j') = fun y => ∏ j, x j y ^ (α j).val := by
    intro α
    have h1 := hmon α
    rw [hBc] at h1
    exact (Submodule.mem_span_range_iff_exists_fun R).1 h1
  choose c hc using hcol
  have hMon : (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val) =
      B * Matrix.of fun j' α => algebraMap R C (c α j') := by
    ext y α
    have e := congrFun (hc α) y
    simp only [Finset.sum_apply, Pi.smul_apply] at e
    rw [Matrix.of_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [Matrix.of_apply, Algebra.smul_def]
    ring
  have hvMon : v (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val).det ≤ v B.det := by
    rw [hMon, Matrix.det_mul, map_mul]
    calc v B.det * v (Matrix.of fun j' α => algebraMap R C (c α j')).det ≤ v B.det * 1 :=
          mul_le_mul' le_rfl (IsIntegralMat.det_le_one (v := v) fun j' α => hv.map_le_one _)
      _ = v B.det := mul_one _
  have hColen : HasColen R v AW.carrier (v B.det) := ⟨B, hBc, rfl⟩
  have hN : ∀ y : Fin r → ZMod p, p • y = 0 := by
    intro y
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have h4 := u4 p C v R hv hpC (Fin r → ZMod p) hN AW (v B.det) _ hColen hOm
  have hcard : Fintype.card (Fin r → ZMod p) = p ^ r := by simp
  rw [hcard] at h4
  set Y := ∏ j, v (algebraMap R C (dj j)) with hYdef
  set K := p ^ (Fintype.card (Fin r) - 1) * (p * (p - 1) / 2) with hKdef
  have hYK : Y ^ K ≤ v B.det := by
    rw [hYdef, ← Finset.prod_pow]
    exact h5 ▸ hvMon
  have hchain : Y ^ (2 * K) ≤ (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
    calc Y ^ (2 * K) = (Y ^ K) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ v B.det ^ 2 := by gcongr
      _ ≤ (v (algebraMap R C (p : R)) ^ d) ^ p ^ r := h4
      _ = (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
        rw [← hSet.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
  rw [hXeq]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hY1 : Y = 1 := by simp [hYdef]
    rw [hY1] at hchain ⊢
    rw [one_pow] at hchain
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp
    · exfalso
      have hlt : (v (algebraMap R C cp) ^ d) ^ (p ^ 0 * (p - 1)) < 1 := by
        refine pow_lt_one₀ zero_le' (pow_lt_one₀ zero_le' ?_ (by omega)) (by simp; omega)
        have h1 := hSet.cp_val
        by_contra hge
        push_neg at hge
        have h2 : 1 ≤ v (algebraMap R C cp) ^ (p - 1) := one_le_pow₀ hge
        rw [h1] at h2
        exact absurd hSet.p_lt (not_lt.2 h2)
      exact absurd hchain (not_le.2 hlt)
  · have h2K : 2 * K = p ^ r * (p - 1) := by
      rw [hKdef, Fintype.card_fin, ← mul_assoc, mul_comm 2, mul_assoc,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p)]
      have : p ^ (r - 1) * p = p ^ r := by rw [← pow_succ]; congr 1; omega
      rw [← mul_assoc, this]
    rw [h2K] at hchain
    exact (pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))).1 hchain

end ReciprocityTheory.PGsh.Up
end
end
end

-- Source module: ReciprocityTheory.DualLattices.LengthDegreeOfFrobenius

section

@[expose] public section

namespace ReciprocityTheory.PGsh.Up

theorem wdet_of_smith_normal_form (hS : EigenQuotientSmithStatement) : CokernelLengthComparisonStatement :=
  cokernelLengthComparison_of wdetLen (wdetDegree_of_smith_restrict hS restrict_hopfOrder_length restrictedHopfOrderApproximation)

theorem u6 : CokernelLengthComparisonStatement := wdet_of_smith_normal_form smith_normal_form_statement

end ReciprocityTheory.PGsh.Up
end
end

-- Source module: ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem lat_conseq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) (c : NNReal) (hc : c ≤ colen M' M) :
    c ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s :=
  le_trans (by gcongr)
    (colength_sq_mul_le_prod C v R hv hnt n a hinj hint s h A F M M' Mτ M'τ hF hA hM' hMst hMτ hM'τ)

theorem lengthDegree_abelianVariety : PermutedCokernelLowerBoundStatement := permutedCokernelLowerBound_of u6 lenEx killedGen idemGen

theorem up_full (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (N : Type) [AddCommGroup N] [Module R N]
    (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N) (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1 := by
  obtain ⟨k, c0, ⟨F0⟩, hc0⟩ := hN
  have h10 := unramifiedCokernelLowerBound_of hU7 lenEx killedGen idemGen
  unfold UnramifiedCokernelLowerBoundStatement at h10
  exact h10 p g C v R O σ cp hp2 hS H U i V1 ⟨k, c0, ⟨E.trans F0⟩, hc0⟩

private lemma prime_rpow_neg_succ_eq_inv_mul_inv_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) + 1)) = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.rpow_neg hp0.le, hn, Real.rpow_natCast, ← inv_pow, pow_succ]
  ring

private lemma prime_inv_lt_one {p : ℕ} [Fact p.Prime] : (p : ℝ)⁻¹ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 := one_div_lt_one_div_of_lt one_pos hp
  simpa using h1

private lemma summable_prime_rpow_neg_succ {p : ℕ} [Fact p.Prime] :
    Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) := by
  have e : (fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1))) =
      fun n : ℕ => (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := funext fun n => prime_rpow_neg_succ_eq_inv_mul_inv_pow n
  rw [e]
  exact (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one).mul_left _

lemma tsum_geom_p {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  rw [tsum_congr (fun n : ℕ => prime_rpow_neg_succ_eq_inv_mul_inv_pow (p := p) n), tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one]
  field_simp

lemma summable_geom_p {p : ℕ} [Fact p.Prime] (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ)
    (hfB : ∀ n, f n ≤ B) : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * f n := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hf0 n))
    (fun n => mul_le_mul_of_nonneg_left (hfB n) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    ((summable_prime_rpow_neg_succ (p := p)).mul_right B)

end ReciprocityTheory.PGsh.Up
end
end
end
