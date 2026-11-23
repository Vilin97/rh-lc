module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HfAlgSmulRight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerpEqPerpNb
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulMemIff
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdPowMemOfLe

section

@[expose] public section

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem mem_std {x : Fin r → K} :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔
      ∀ i, x i ∈ (algebraMap O K).range := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz => intro i; exact add_mem (hy i) (hz i)
    | smul a y _ hy =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def]
      exact mul_mem ⟨a, rfl⟩ (hy i)
  · intro hx
    choose a ha using hx
    have : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
      funext j
      simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem hf_mulVec (cK : K ≃+* K) (J g : Matrix (Fin r) (Fin r) K)
    (hU : (g.map cK).transpose * J * g = J) (x y : Fin r → K) :
    hf cK J (g.mulVec x) (g.mulVec y) = hf cK J x y := by
  have e1 : (fun i => cK (g.mulVec x i)) = (g.map cK).mulVec (fun i => cK (x i)) := by
    funext i
    exact RingHom.map_mulVec cK.toRingHom g x i
  unfold hf
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hU]

theorem std_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) O) (hJ : IsUnit J.det) :
    IsSD cK (J.map (algebraMap O K)) (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) := by
  classical
  intro x
  constructor
  · intro hx y hy
    rw [mem_std] at hx hy
    unfold hf
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem (conj_mem_range c cK hcK (hx i)) ?_
    exact Subring.sum_mem _ fun j _ => mul_mem ⟨_, rfl⟩ (hy j)
  · intro h
    rw [mem_std]
    set w : Fin r → K := Matrix.vecMul (fun i => cK (x i)) (J.map (algebraMap O K)) with hw
    have hwR : ∀ j, w j ∈ (algebraMap O K).range := by
      intro j
      have hej : Pi.single j (1 : K) ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) :=
        Submodule.subset_span ⟨j, Pi.basisFun_apply K (Fin r) j⟩
      have := h _ hej
      unfold hf at this
      rwa [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    have hJJ : J.map (algebraMap O K) * J⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    have hx' : (fun i => cK (x i)) = Matrix.vecMul w (J⁻¹.map (algebraMap O K)) := by
      rw [hw, Matrix.vecMul_vecMul, hJJ, Matrix.vecMul_one]
    intro i
    have hi : cK (x i) ∈ (algebraMap O K).range := by
      rw [show cK (x i) = (fun i => cK (x i)) i from rfl, hx']
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
      exact Subring.sum_mem _ fun j _ => mul_mem (hwR j) ⟨_, rfl⟩
    rw [← hc2 (x i)]
    exact conj_mem_range c cK hcK hi

theorem exists_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) (y : K) :
    ∃ k : ℕ, algebraMap O K (ϖ ^ k) * y ∈ (algebraMap O K).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨k, u * a, ?_⟩
  have hb' : algebraMap O K b ≠ 0 := by
    intro h; exact hb0 (IsFractionRing.injective O K (by simpa using h))
  rw [← hu, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem std_pow_mem_of_le {ϖ : O} {x : Fin r → K} {k : Fin r → ℕ}
    (hk : ∀ i, algebraMap O K (ϖ ^ k i) * x i ∈ (algebraMap O K).range) :
    (ϖ ^ (∑ i, k i)) • x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  rw [mem_std]
  intro i
  have hle : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Pi.smul_apply, Algebra.smul_def, ← Nat.sub_add_cancel hle, pow_add, map_mul, mul_assoc]
  exact mul_mem ⟨_, rfl⟩ (hk i)

theorem idx_std {ϖ : O} (hϖ : Irreducible ϖ) :
    idx ϖ (Submodule.span O (Set.range (Pi.basisFun K (Fin r))) : Submodule O (Fin r → K)) =
      Nat.card (IsLocalRing.ResidueField O) ^ r := by
  classical
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r)))
  have hex : ∀ (x : L0.toAddSubgroup) (i : Fin r), ∃ a : O, algebraMap O K a = (x : Fin r → K) i :=
    fun x i => mem_std.1 x.2 i
  choose a ha using hex
  have hadd : ∀ x y i, a (x + y) i = a x i + a y i := by
    intro x y i
    apply IsFractionRing.injective O K
    rw [map_add (f := _), ha, ha, ha]; rfl
  let ψ : L0.toAddSubgroup →+ (Fin r → IsLocalRing.ResidueField O) :=
    AddMonoidHom.mk' (fun x i => IsLocalRing.residue O (a x i)) (by
      intro x y; funext i; simp [hadd])
  have hker : (L0.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
      L0.toAddSubgroup = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (x : Fin r → K) ∈ L0.map _ ↔ (fun i => IsLocalRing.residue O (a x i)) = 0
    rw [funext_iff]
    simp only [Pi.zero_apply, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy, hyx⟩ i
      obtain ⟨b, hb⟩ := mem_std.1 hy i
      refine ⟨b, IsFractionRing.injective O K ?_⟩
      rw [ha, ← hyx, map_mul, hb]
      simp [Algebra.smul_def]
    · intro h
      choose b hb using h
      refine ⟨fun i => algebraMap O K (b i), mem_std.2 fun i => ⟨b i, rfl⟩, ?_⟩
      funext i
      show (ϖ • (fun i => algebraMap O K (b i))) i = (x : Fin r → K) i
      rw [Pi.smul_apply, Algebra.smul_def, ← map_mul, ← hb, ha]
  have hsurj : Function.Surjective ψ := by
    intro z
    choose b hb using fun i => IsLocalRing.residue_surjective (z i)
    have hm : (fun i => algebraMap O K (b i)) ∈ L0.toAddSubgroup := mem_std.2 fun i => ⟨b i, rfl⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    funext i
    change IsLocalRing.residue O (a ⟨_, hm⟩ i) = z i
    have : a ⟨_, hm⟩ i = b i := IsFractionRing.injective O K (by rw [ha])
    rw [this, hb]
  unfold idx
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

end GlobalTheory.HermNbr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualSumLe

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem good_map (cK : K ≃+* K) {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hϖ : Irreducible ϖ)
    (g : GL (Fin r) K) (hU : ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J *
      (g : Matrix (Fin r) (Fin r) K) = J) :
    Good cK J ϖ N (L.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) := by
  set G := ((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hG
  set Gi := (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hGi
  have h1 : ∀ x, G (Gi x) = x := by
    intro x
    change (g : Matrix (Fin r) (Fin r) K).mulVec ((((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x, Gi (G x) = x := by
    intro x
    change (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec ((g : Matrix (Fin r) (Fin r) K).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have memG : ∀ x, x ∈ L.map G ↔ Gi x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [h2]; exact hy
    · intro h; exact ⟨Gi x, h, h1 x⟩
  have hfG : ∀ x y, hf cK J (G x) (G y) = hf cK J x y := fun x y => hf_mulVec cK J _ hU x y
  obtain ⟨hSD, habs, hidx⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [memG, hSD (Gi x)]
    constructor
    · intro h y hy
      rw [← h1 x, ← h1 y, hfG]
      exact h _ ((memG y).1 hy)
    · intro h y hy
      have := h (G y) ((memG _).2 (by rw [h2]; exact hy))
      rwa [← h1 x, hfG] at this
  · intro x
    obtain ⟨k, hk⟩ := habs (Gi x)
    refine ⟨k, (memG _).2 ?_⟩
    rw [map_smul]
    exact hk
  · have hinj : Function.Injective G.toAddMonoidHom := fun x y h => by
      have := congrArg Gi h
      simpa [h2] using this
    set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
    have hcomm : (L.map G).map f = (L.map f).map G := by
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext x
      simp [hf', hG]
    have e : ∀ P : Submodule O (Fin r → K),
        (P.map G).toAddSubgroup = P.toAddSubgroup.map G.toAddMonoidHom := fun P => by
      ext x; simp [Submodule.mem_map]
    unfold idx at hidx ⊢
    rw [← hf'] at hidx ⊢
    rw [hcomm, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

end GlobalTheory.HermNbr

theorem GlobalTheory.HermNbr.selfDual_sum_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (c : O ≃+* O) (cK : K ≃+* K), (∀ x, c (c x) = x) → (∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) → (∃ x, IsUnit (c x - x)) → ∀ (r n : ℕ) (J : Matrix (Fin r) (Fin r) O), IsUnit J.det → J.transpose.map c = J → 2 * r + 5 ≤ n → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = J.map (algebraMap O K)) → (∀ g ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≠ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) → (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, ((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-(2 : ℝ)) := by
  intro O K _ _ _ _ _ _ _ c cK hc hcK _ r n J hJdet hJh hn C hU hne hinj
  classical
  set J' := J.map (algebraMap O K) with hJ'
  have hc2 : ∀ x : K, cK (cK x) = x := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀, map_div₀, hcK, hcK, hcK, hcK, hc, hc]
  have hJ'h : J'.transpose.map cK = J' := by
    ext i j
    simp only [hJ', Matrix.map_apply, Matrix.transpose_apply, hcK]
    have := congrFun (congrFun hJh i) j
    simp only [Matrix.map_apply, Matrix.transpose_apply] at this
    rw [this]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set Q := Nat.card (IsLocalRing.ResidueField O) with hQdef
  have hQ2 : 2 ≤ Q := Finite.one_lt_card
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r))) with hL0def
  have hL0 : GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L0 := by
    refine ⟨GlobalTheory.HermNbr.std_sd c cK hcK hc2 J hJdet, ?_, GlobalTheory.HermNbr.idx_std hϖ⟩
    intro x
    choose k hk using fun i => GlobalTheory.HermNbr.exists_pow_mul_mem hϖ (x i)
    exact ⟨_, GlobalTheory.HermNbr.std_pow_mem_of_le hk⟩
  set φ : GL (Fin r) K → Submodule O (Fin r → K) := fun g =>
    L0.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) with hφ
  have hgood : ∀ g ∈ C, GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) (φ g) := fun g hg =>
    GlobalTheory.HermNbr.good_map cK hL0 hϖ g (hU g hg)

  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
  set s : ℝ := (n : ℝ) / 2 with hs
  set D : ℝ := (Q : ℝ) ^ r * Q / ((Q : ℝ) - 1) with hD
  set y : ℝ := (Q : ℝ) ^ (-(2 : ℝ)) with hy
  have hs0 : 0 < s := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast (by omega : 5 ≤ n)
    rw [hs]; linarith
  have hD0 : 0 ≤ D := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hQ0 _
  have hy4 : y ≤ 1 / 4 := by
    rw [hy, Real.rpow_neg hQ0.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hρ : D * (Q : ℝ) ^ (-s) ≤ 2 * y := by
    have hsr : (r : ℝ) + 5 / 2 ≤ s := by
      have : ((2 * r + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      rw [hs]; linarith
    have h1 : (Q : ℝ) ^ (-s) ≤ (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) = ((Q : ℝ) ^ r)⁻¹ * ((Q : ℝ) ^ (-(2 : ℝ)) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [← Real.rpow_add hQ0, show -((r : ℝ) + 5 / 2) = -(r : ℝ) + (-(2 : ℝ) + -(1 / 2 : ℝ)) by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le, Real.rpow_natCast]
    have h3 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : (Q : ℝ) / ((Q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hQ1]; linarith
    have hQr0 : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
    calc D * (Q : ℝ) ^ (-s) ≤ D * (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) := mul_le_mul_of_nonneg_left h1 hD0
      _ = (Q : ℝ) / ((Q : ℝ) - 1) * (y * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
          rw [h2, hD, hy]; field_simp
      _ ≤ 2 * (y * 1) := by
          apply mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 hy0.le) (by positivity) (by norm_num)
      _ = 2 * y := by ring
  have hρ1 : D * (Q : ℝ) ^ (-s) < 1 := by linarith

  have key := GlobalTheory.HermNbr.graph_sum {L | GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L}
    (fun L Λ => Λ.toAddSubgroup.relIndex L.toAddSubgroup) (GlobalTheory.HermNbr.Nbrs cK J' ϖ) Q hQ2 s D
    hs0 hD0 hρ1 (fun L _ => AddSubgroup.relIndex_self _)
    (fun L hL Λ hΛ hne hi => by
      obtain ⟨L', h1, h2, h3, h4⟩ :=
        GlobalTheory.HermNbr.step_exists c cK hcK hc2 hJ'h hϖ hL hΛ hne hi
      exact ⟨L', h1, h2, h3, h4⟩)
    (fun L hL t ht => by
      have h := GlobalTheory.HermNbr.card_nbrs c cK hcK hc2 hJ'h hϖ hL (by positivity) t ht
      rw [hD, le_div_iff₀ hQ1]
      have : ((t.card * (Q - 1) : ℕ) : ℝ) ≤ ((Q ^ r * Q : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ Q)] at this
      linarith)
    L0 hL0 (C.image φ)
    (by
      intro Λ hΛ
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hΛ)
      exact hgood g hg)
    (by
      intro h
      obtain ⟨g, hg, hg'⟩ := Finset.mem_image.1 h
      exact hne g hg hg')
  rw [Finset.sum_image (fun g hg g' hg' h => hinj g hg g' hg' h)] at key
  have hsum : ∀ g ∈ C, (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) =
      (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-s) := by
    intro g _; rw [hs, neg_div]
  rw [← Finset.sum_congr rfl hsum] at key
  refine le_trans key ?_
  set ρ := D * (Q : ℝ) ^ (-s)
  have hρ0 : 0 ≤ ρ := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith
end
end
