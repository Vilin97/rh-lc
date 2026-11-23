module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruenceStatement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousLiftCompatible

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem homogeneous_lift_compatible : ∀ (l : ℕ) [Fact l.Prime] (w : ℕ) (p : (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))), (∀ n, (p n).IsHomogeneous w) → (∀ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (p (n + 1)) = p n) → ∃ q : MvPolynomial (Fin 2) ℤ_[l], q.IsHomogeneous w ∧ (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q = p n) ∧ ∀ q' : MvPolynomial (Fin 2) ℤ_[l], (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q' = p n) → q' = q := by
  intro l _ w p hhom hcomp
  have hc1 : ∀ (m : Fin 2 →₀ ℕ) (n : ℕ),
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) ((p (n + 1)).coeff m) = (p n).coeff m := by
    intro m n
    rw [← hcomp n, MvPolynomial.coeff_map]
  have hc : ∀ (m : Fin 2 →₀ ℕ) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁)) ((p k₂).coeff m) = (p k₁).coeff m := by
    intro m k₁ k₂ hk
    induction k₂, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [← ih, ← hc1 m k]
      show _ = ((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)))) _
      rw [ZMod.castHom_comp]

  let f : ∀ k, MvPolynomial (Fin 2 →₀ ℕ) ℤ →+* ZMod (l ^ k) := fun k =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun m => (p k).coeff m)
  have hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply MvPolynomial.ringHom_ext
    · intro r; simp [f]
    · intro m
      simp only [f, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hc m k₁ k₂ hk
  let g := PadicInt.lift hf
  let c : (Fin 2 →₀ ℕ) → ℤ_[l] := fun m => g (MvPolynomial.X m)
  have hcn : ∀ m n, PadicInt.toZModPow n (c m) = (p n).coeff m := by
    intro m n
    have := congrArg (fun φ => φ (MvPolynomial.X m)) (PadicInt.lift_spec hf n)
    simpa [c, g, f] using this
  have hdeg : ∀ m, c m ≠ 0 → m.degree = w := by
    intro m hm
    by_contra hne
    apply hm
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, map_zero]
    by_contra h0
    apply hne
    rw [Finsupp.degree_eq_weight_one]
    exact hhom n h0
  have hfin : (Function.support c).Finite :=
    (Finsupp.finite_of_degree_le w).subset fun m hm => le_of_eq (hdeg m hm)
  let q : MvPolynomial (Fin 2) ℤ_[l] := ∑ m ∈ hfin.toFinset, MvPolynomial.monomial m (c m)
  have hq : ∀ m, q.coeff m = c m := by
    intro m
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro m hm
    rw [hq] at hm
    have h := hdeg m hm
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  · intro n
    ext m
    rw [MvPolynomial.coeff_map, hq, hcn]
  · intro q' hq'
    apply MvPolynomial.ext
    intro m
    rw [hq]
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, ← hq' n, MvPolynomial.coeff_map]

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOnStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' → Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧ ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  first | exact @GlobalTheory.KZ.H3.adj_of_near | exact GlobalTheory.KZ.H3.adj_of_near | (intros; apply GlobalTheory.KZ.H3.adj_of_near <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamily

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.CocLift

open MvPolynomial CongruenceSubgroup

theorem gamma_of_dvd {a b : ℕ} (h : a ∣ b) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma b) : δ ∈ Gamma a := by
  rw [Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, map_one]
  · rw [← key, h2, map_zero]
  · rw [← key, h3, map_zero]
  · rw [← key, h4, map_one]

theorem gamma_le_gam {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    δ ∈ Gam N l := by
  have h1 := Gamma_mem.mp (gamma_of_dvd hN hδ)
  have h2 := Gamma_mem.mp (gamma_of_dvd hl hδ)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · rw [Gamma0_mem]; exact h2.2.2.1

theorem entries_of_gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    ∀ i j, (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem step (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w)
    (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) (hΦ : IsFam l w (Gam N l) Φ)
    (n : ℕ) (y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (hy : IsCoc w (Gam N l) y) (hyn : Near y (Φ n)) :
    ∃ y' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))), IsCoc w (Gam N l) y' ∧ Near y' (Φ (n + 1)) ∧
      ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (y' γ) = y γ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨z', hz', hz'n⟩ := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ (n + 1)
  set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc
  have L := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have L' := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))
  let r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) := fun δ => MvPolynomial.map c (z' δ)
  have hr : IsCoc w (Gam N l) r := by
    refine ⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩
    simp only [r]
    rw [hz'.2 γ hγ δ hδ, map_add (f := _), L'.2.2.2.2.1 _ c]
  have hnear : Near r y := by
    obtain ⟨M1, hM1, h1⟩ := hz'n
    obtain ⟨M2, hM2, h2⟩ := hΦ.2.2.2 n
    obtain ⟨M3, hM3, h3⟩ := hyn
    refine ⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ
    have d2 := gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ
    have d3 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only [r]
    rw [h1 δ d1]
    exact (h2 δ d2).trans (h3 δ d3).symm
  obtain ⟨p, hph, hpγ⟩ := GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn N l w n hN hp hl2 hlN hw r y hr hy hnear
  let pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))) :=
    ∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))
  have hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1))) := by
    intro m
    simp only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff] at h
      rw [h, ZMod.val_zero, Nat.cast_zero]
  have hmap : MvPolynomial.map c pt = p := by
    ext m
    rw [MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]
  have hpth : pt.IsHomogeneous w := by
    intro m hm
    apply hph
    intro h0
    apply hm
    rw [hpc, h0, ZMod.val_zero, Nat.cast_zero]
  refine ⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩
  · exact (hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)
  · simp only
    rw [hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]
    abel
  · obtain ⟨M1, hM1, h1⟩ := hz'n
    refine ⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only
    rw [L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]
  · intro γ hγ
    simp only
    rw [map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]
    simp only [r]
    abel

end GlobalTheory.KZ.H3.CocLift

namespace GlobalTheory.KZ.H3


open Classical in
theorem cocycle_lift_of_fam : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ →
    ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧
      ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  intro N l w _ hN hl2 hlN hw Φ hΦ
  have hp : l.Prime := Fact.out
  have lev := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ
  choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ
  let seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)} :=
    fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) //
        IsCoc w (Gam N l) y ∧ Near y (Φ n)})
      ⟨(lev 0).choose, (lev 0).choose_spec⟩
      (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n
  have hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      ((seq (n + 1)).1 γ) = (seq n).1 γ :=
    fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2
  let fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) :=
    fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0
  have hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ := fun δ hδ n => if_pos hδ
  have hhom : ∀ δ n, (fam δ n).IsHomogeneous w := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ]; exact (seq n).2.1.1 δ hδ
    · simp only [fam, if_neg hδ]; exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      (fam δ (n + 1)) = fam δ n := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ, hfam δ hδ]; exact hseq n δ hδ
    · simp only [fam, if_neg hδ, map_zero]
  choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)
  have L := GlobalTheory.KZ.polySlash_laws ℤ_[l]
  refine ⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩
  · refine ((hq (γ * δ)).2.2 _ fun n => ?_).symm
    have hγδ : γ * δ ∈ Gam N l := (Gam N l).mul_mem hγ hδ
    rw [map_add (f := _), L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ,
      (seq n).2.1.2 γ hγ δ hδ]
  · obtain ⟨M, hM, hMδ⟩ := (seq n).2.2
    refine ⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩
    have d1 := CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ
    simp only
    rw [(hq δ).2.1 n, hfam δ d2]
    exact hMδ δ d1

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamilyStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧ ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.cocycle_lift_of_fam | exact GlobalTheory.KZ.H3.cocycle_lift_of_fam | (intros; apply GlobalTheory.KZ.H3.cocycle_lift_of_fam <;> assumption)
end
end
