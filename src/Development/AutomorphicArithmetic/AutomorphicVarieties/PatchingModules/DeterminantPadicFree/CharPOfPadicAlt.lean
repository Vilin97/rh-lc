module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetPush
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CompSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PushSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PadicHomUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SplitEx
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtTrans

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extTrans :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' x'' : NP F n) (j : x.A →+* x'.A) (j' : x'.A →+* x''.A), x.Ext2 x' j → x'.Ext2 x'' j' → x.Ext2 x'' (j'.comp j) := by
  intro l _ F n x x' x'' j j' h1 h2
  obtain ⟨⟨hi, hl, hf, hρ, ha, hψ⟩, hw, ht⟩ := h1
  obtain ⟨⟨hi', hl', hf', hρ', ha', hψ'⟩, hw', ht'⟩ := h2
  refine ⟨⟨hi'.comp hi, @RingHom.isLocalHom_comp _ _ _ _ _ _ j' j hl' hl, hf'.comp hf, ?_, ha'.trans ha, ?_⟩,
    ?_, ht'.trans ht⟩
  · rw [hρ', hρ]
    simp only [pushRep, GeneralLinearGroup.map_comp, MonoidHom.comp_assoc]
  · intro v i
    rw [hψ', hψ]
    ext g
    simp [pushCh]
  · intro v
    rw [hw', hw, GeneralLinearGroup.map_comp]
    rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.KapPush

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.kapPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ k : Kap x, ∃ (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) ∧ ∀ i v, k'.Y i v = (k.Y (Fin.cast e i) v).map j := by
  intro l _ F n x x' j hE k
  obtain ⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1
  obtain ⟨pS, pB, pL⟩ := UpperTheory.V.Pa.Det.pushSel x x' j hE
  have cS := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1
  have cB := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2
  obtain ⟨S, hS⟩ := (UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2
  have ha : x'.a = x.a := hE.1.2.2.2.2.1
  refine ⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_,
    fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i v r s
    refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
    have := (k.Y_mem i v r s).1 (by rw [← ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  · intro c hcB
    have h0 : ∀ i, (fun a => p i (c a)) = 0 := by
      intro i
      apply k.indep
      convert cB i _ hcB using 1
      funext g
      ext r s : 1

      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm (c a), hp, mul_comm]
    funext a
    rw [hb (c a)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]
  · intro z hz
    choose s c hsc using fun i => k.gen _ (cS i z hz)
    have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    set N := ∑ i, s i with hN
    let d : Fin m → x'.A := fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))
    have h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
    have key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y := by
      intro y
      conv_rhs => rw [hb y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]
      simp only [d, map_mul]
      linear_combination (((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4
        + (x'.t ^ (e * N) * b i * j (p i y)) * h3
    refine ⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩
    have hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S := by
      refine S.sum_mem fun i _ => S.smul_mem _ ?_
      have := pB _ (hsc i)
      rw [← hS] at this
      exact this
    rw [← hS, SetLike.mem_coe]
    convert hm using 1
    funext g
    ext r t : 1

    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul,
    Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [map_mul, mul_assoc]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadicAlt

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpr : p.Prime := CharP.char_is_prime K p
  by_cases h : p = l
  · subst h
    exact hp
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out hpr).2 (Ne.symm h)
    have hu' := hu.map f
    rw [map_natCast, CharP.cast_eq_zero] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.Det.onePt :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {q : ℕ} (sg : Fin q → F.G₀), (∀ a, ((mat x.ρ (sg a)).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable) → Detects k (Set.range sg) → ∃ d : ℕ, d ≠ 0 ∧ ∀ D, d ∣ D → D ≠ 0 → ∃ (x' : NP F n) (j : x.A →+* x'.A) (k' : Kap x') (al : Fin q → Fin n → x'.A), x.Ext x' j ∧ Nat.card x'.K = l ^ D ∧ Detects k' (Set.range sg) ∧ ∀ a, Function.Injective (al a) ∧ (mat x'.ρ (sg a)).charpoly = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ F n x k q sg hsep hdet
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  have hmat : ∀ (y y' : NP F n) (j : y.A →+* y'.A), y.Ext y' j → ∀ g, mat y'.ρ g = (mat y.ρ g).map j := by
    intro y y' j h g
    rw [h.2.2.2.1]
    rfl
  obtain ⟨A1, _, _, _, _, j1, al1, hj1i, hj1l, hj1f, hal1⟩ :=
    Det.splitEx l (n := n) (fun a => (mat x.ρ (sg a)).charpoly)
      (fun a => ⟨Matrix.charpoly_monic _, by simp [Matrix.charpoly_natDegree_eq_dim], hsep a⟩)
  obtain ⟨x1, J1, e1, hE1, he1, -⟩ := Det.extEx x A1 j1 hj1i hj1l hj1f
  haveI : CharP x1.K l := charP_of_padic (algebraMap ℤ_[l] x1.K)
  haveI := Fintype.ofFinite x1.K
  obtain ⟨d, -, hcard⟩ := FiniteField.card x1.K l
  refine ⟨(d : ℕ), d.ne_zero, ?_⟩
  intro D hdD hD0
  obtain ⟨A2, _, _, _, _, j2, hj2i, hj2l, hj2f, hres2, -⟩ :=
    Det.resExt l (K := x1.K) d D (by rw [Nat.card_eq_fintype_card]; exact hcard) hdD hD0
  obtain ⟨x2, J2, e2, hE2, -, hc2⟩ := Det.extEx x1 A2 j2 hj2i hj2l hj2f
  have hE := Det.extTrans x x1 x2 J1 J2 hE1 hE2
  obtain ⟨k', e, hk, -⟩ := Det.kapPush x x2 _ hE k
  refine ⟨x2, J2.comp J1, k', fun a b => J2 (e1.symm (al1 a b)), hE.1, by rw [hc2, hres2],
    Det.detPush x x2 _ hE k k' e hk _ hdet, fun a => ⟨?_, ?_⟩⟩
  · exact hE2.1.1.comp (e1.symm.injective.comp (hal1 a).1)
  · have h1 : J1 = (e1.symm : A1 →+* x1.A).comp j1 := by
      refine RingHom.ext fun t => ?_
      simp [← he1 t]
    have key : Polynomial.map J1 (mat x.ρ (sg a)).charpoly =
        ∏ b, (Polynomial.X - Polynomial.C (e1.symm (al1 a b))) := by
      rw [h1, ← Polynomial.map_map, (hal1 a).2, Polynomial.map_prod]
      simp
    rw [hmat x x2 _ hE.1, Matrix.charpoly_map, ← Polynomial.map_map, key, Polynomial.map_prod]
    simp
end
end
