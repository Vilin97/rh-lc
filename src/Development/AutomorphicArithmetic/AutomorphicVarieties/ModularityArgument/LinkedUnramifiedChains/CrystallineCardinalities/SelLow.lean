module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdicContinuousSumThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.ArchUp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LcOfKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LowerTriangularAbsorbsTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.MatrixEntryZeroTwoSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.NormCnt
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocHigh

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {D : Type} [Group D] [TopologicalSpace D]

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locHigh :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ C : ℕ, ∀ k, 0 < k → Nat.card (Ok l O k) ^ (7 + 3 * d) ≤ C * (ZF (l := l) I k t).ncard := by
  classical
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hG hT i hU
  obtain ⟨c, hc0, hy⟩ := yEx l O D I ε d t hl hLE hG hT i hU
  have hOk := okFin l O hl
  haveI : Finite (O ⧸ Ideal.span {c}) := hOk.2.1 c hc0
  refine ⟨Nat.card (O ⧸ Ideal.span {c}), fun k hk => ?_⟩
  haveI : Finite (Ok l O k) := hOk.1 k
  obtain ⟨hZfin, -⟩ := locLow l O D I ε d t hl hLE hG hT k hk
  have hW := low0 l O D I ε d t hl hLE hG hT i hU k hk
  obtain ⟨y, hyZ, s0, hys⟩ := hy k hk
  set mc : Ok l O k := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c with hmc
  have hmem : ∀ w ∈ ZF (l := l) I k t, ∀ a : Ok l O k, w + a • y ∈ ZF (l := l) I k t := by
    intro w hw a
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hyZ
    refine ⟨hw1.add (hy1.comp (fun x => a • x)), ?_, ?_, ?_⟩
    · intro s s'
      simp only [Pi.add_apply, Pi.smul_apply, hw2 s s', hy2 s s', cj, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_add]
      abel
    · intro s p q hpq
      simp [hw3 s p q hpq, hy3 s p q hpq]
    · intro s hs p
      simp [hw4 s hs p, hy4 s hs p]
  set W := {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ} with hWdef
  let J : Ideal (Ok l O k) := Ideal.span {mc}
  let g : Ok l O k → Ok l O k := fun b => if h : ∃ a, a * mc = b then h.choose else 0
  have hg : ∀ b ∈ (J : Set (Ok l O k)), g b * mc = b := by
    intro b hb
    have h : ∃ a, a * mc = b := Ideal.mem_span_singleton'.mp hb
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hcount : (W ×ˢ (J : Set (Ok l O k))).ncard ≤ (ZF (l := l) I k t).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p => p.1 + g p.2 • y) ?_ ?_ hZfin
    · rintro ⟨w, b⟩ ⟨hw, -⟩
      exact hmem w hw.1 _
    · rintro ⟨w, b⟩ ⟨hw, hb⟩ ⟨w', b'⟩ ⟨hw', hb'⟩ h
      dsimp only at h hw hb hw' hb'
      have h1 := congrFun (congrFun (congrFun h s0) i.castSucc) i.castSucc
      have h2 := congrFun (congrFun (congrFun h s0) i.succ) i.succ
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
      have hwa : w s0 i.castSucc i.castSucc = w s0 i.succ i.succ := hw.2 s0
      have hwb : w' s0 i.castSucc i.castSucc = w' s0 i.succ i.succ := hw'.2 s0
      have hbb : b = b' := by
        linear_combination -(hg b hb) + hg b' hb' - (g b - g b') * hys + h1 - h2 - hwa + hwb
      subst hbb
      have : w = w' := add_right_cancel h
      simp [this]
  have hJ : Nat.card (Ok l O k) ≤ Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard := by
    have h1 : Nat.card (Ok l O k) = Nat.card J * Nat.card (Ok l O k ⧸ J) :=
      Submodule.card_eq_card_quotient_mul_card J
    have h2 : Nat.card (Ok l O k ⧸ J) ≤ Nat.card (O ⧸ Ideal.span {c}) := by
      let φ : O →+* Ok l O k ⧸ J := (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk _)
      have hφ : ∀ a ∈ Ideal.span {c}, φ a = 0 := by
        intro a ha
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, show φ c = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
          mul_zero]
      apply Nat.card_le_card_of_surjective (Ideal.Quotient.lift _ φ hφ)
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    rw [h1, mul_comm, ← Nat.card_coe_set_eq]
    exact Nat.mul_le_mul_right _ h2
  calc Nat.card (Ok l O k) ^ (7 + 3 * d)
      = Nat.card (Ok l O k) ^ (6 + 3 * d) * Nat.card (Ok l O k) := by ring
    _ ≤ W.ncard * (Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard) := Nat.mul_le_mul hW hJ
    _ = Nat.card (O ⧸ Ideal.span {c}) * (W ×ˢ (J : Set (Ok l O k))).ncard := by rw [Set.ncard_prod]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.SelLow

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem sel_arith {V : Type} [Fintype V] (q C L N : ℕ) (hq : 0 < q) (d z : V → ℕ) (v : V)
    (h1 : ∀ w, q ^ (9 + 3 * d w) ≤ z w) (h2 : q ^ (10 + 3 * d v) ≤ C * z v)
    (h3 : q ^ 9 * ∏ w, z w ≤ L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) (h4 : L ≤ N * q ^ 8) :
    q ^ 2 ≤ C * N := by
  classical
  have hv : v ∈ Finset.univ := Finset.mem_univ v
  obtain ⟨E, hE⟩ : ∃ E, E = ∏ w, q ^ (9 + 3 * d w) := ⟨_, rfl⟩
  have hEeq : E = (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V := by
    rw [hE]
    simp only [pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_pow_eq_pow_sum]
    ring
  have hEpos : 0 < E := by
    rw [hE]
    exact Finset.prod_pos fun w _ => pow_pos hq _
  have key : q * E ≤ C * ∏ w, z w := by
    rw [hE, ← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ _ hv]
    calc _ = q ^ (10 + 3 * d v) * ∏ w ∈ Finset.univ.erase v, q ^ (9 + 3 * d w) := by ring
      _ ≤ (C * z v) * ∏ w ∈ Finset.univ.erase v, z w :=
          Nat.mul_le_mul h2 (Finset.prod_le_prod' fun w _ => h1 w)
      _ = _ := by ring
  have main : q ^ 2 * (q ^ 8 * E) ≤ (C * N) * (q ^ 8 * E) := by
    calc q ^ 2 * (q ^ 8 * E) = q ^ 9 * (q * E) := by ring
      _ ≤ q ^ 9 * (C * ∏ w, z w) := Nat.mul_le_mul_left _ key
      _ = C * (q ^ 9 * ∏ w, z w) := by ring
      _ ≤ C * (L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := Nat.mul_le_mul_left _ h3
      _ ≤ C * (N * q ^ 8 * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := by gcongr
      _ = (C * N) * (q ^ 8 * E) := by rw [hEeq]; ring
  exact Nat.le_of_mul_le_mul_right main (Nat.mul_pos (pow_pos hq 8) hEpos)

private theorem sel_cut (q a e z n C : ℕ) (hq : 0 < q) (h : q ^ (a + e) ≤ C * n) (h' : n * q ^ 9 ≤ z * q ^ 6) :
    q ^ (a + 3 + e) ≤ C * z := by
  have b : q ^ 6 * q ^ (a + 3 + e) ≤ q ^ 6 * (C * z) :=
    calc q ^ 6 * q ^ (a + 3 + e) = q ^ (a + e) * q ^ 9 := by ring
      _ ≤ C * n * q ^ 9 := Nat.mul_le_mul_right _ h
      _ = C * (n * q ^ 9) := by ring
      _ ≤ C * (z * q ^ 6) := Nat.mul_le_mul_left _ h'
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left b (pow_pos hq _)

private theorem card_mat (A : Type) : Nat.card (Matrix (Fin 3) (Fin 3) A) = Nat.card A ^ 9 := by
  show Nat.card (Fin 3 → Fin 3 → A) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

theorem UpperTheory.V.Z.J.selLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (v : F.V) (i : Fin 2), UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i → ∃ C : ℕ, ∀ k, 0 < k → (ZN B k).Finite ∧ Nat.card (Ok l O k) ^ 2 ≤ C * (ZN B k).ncard := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hρ hB hc cw hcw hG hE v i hU
  have T := triOk l O F C₀ hF hl ρ B hρ hB hc
  obtain ⟨C, hC⟩ := locHigh l O (F.Gv v) (F.Iv v) _ (F.dv v) (triOf B v) hl (hE v) (T v).2.1 (T v).1 i hU
  refine ⟨C, fun k hk => ?_⟩
  have hlow := fun w => locLow l O (F.Gv w) (F.Iv w) _ (F.dv w) (triOf B w) hl (hE w) (T w).2.1 (T w).1 k hk
  choose Z hZ1 hZ2 hZ3 hZ4 using fun w => zvCnt l O F C₀ hF hl ρ B hρ hB hc k hk w (hlow w).1
  obtain ⟨hfin, -, hkill, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfin k
  have hq : 0 < Nat.card (Ok l O k) := Nat.card_pos
  haveI : Finite (Matrix (Fin 3) (Fin 3) (Ok l O k)) := inferInstanceAs (Finite (Fin 3 → Fin 3 → Ok l O k))
  have hk2 : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b
    exact hkill k (x a b)
  have hop : IsOpen ((adK B k).ker : Set F.Γ) := by
    first
      | exact adOpen l O F C₀ hF hl B k hc
      | exact (adOpen l O F C₀ hF hl ρ B hρ hB hc k).1
  have hmain : (ZL F (adK B k) fun w => Z w).Finite ∧
      Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) * ∏ w, Nat.card (Z w) ≤
        (ZL F (adK B k) fun w => Z w).ncard * (HomMu l k F.eps (adK B k)).ncard *
        (∏ w, {x | adK B k (cw w) x = x}.ncard) * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) ^ Fintype.card F.V :=
    hG k hk (Matrix (Fin 3) (Fin 3) (Ok l O k)) (adK B k) hk2 hop Z hZ2 hZ3
  have hZe : (fun w => (Z w : Set (F.Gv w → Matrix (Fin 3) (Fin 3) (Ok l O k)))) = Zv B k := funext hZ1
  rw [hZe, dualZero l O F C₀ hF hl ρ B hρ hB hc k hk, Set.ncard_singleton, mul_one, card_mat] at hmain
  have harch : (∏ w, {x | adK B k (cw w) x = x}.ncard) ≤ (Nat.card (Ok l O k) ^ 3) ^ (∑ w, F.dv w) := by
    have e : ∑ w, F.dv w = Fintype.card F.Inf := hF.card_inf.symm
    rw [e, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun w _ => ?_
    exact archUp l O hl hF.l_odd (B.r (cw w)) (by rw [← map_mul, (hcw w).1, map_one])
      ((B.nu _).trans (hcw w).2) k hk
  refine ⟨hmain.1.subset fun z hz => hz.1, ?_⟩
  refine sel_arith _ C _ _ hq F.dv (fun w => Nat.card (Z w)) v (fun w => ?_) ?_ ?_
    (normCnt l O F C₀ hF hl ρ B hρ hB hc k hk (fun w => ⟨Z w, hZ1 w⟩) hmain.1)
  · have := sel_cut _ 6 (3 * F.dv w) _ _ 1 hq ((hlow w).2.trans (one_mul _).ge) (hZ4 w)
    rwa [one_mul] at this
  · exact sel_cut _ 7 (3 * F.dv v) _ _ C hq (hC k hk) (hZ4 v)
  · exact hmain.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ harch))
end
end
