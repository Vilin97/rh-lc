module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.GenTwist
variable {X : Scheme.{0}} {M H : LB X}

theorem tw_one_g (p q : M.ι) (k l : H.ι) :
    (((tw M H 1).g (p, k) (q, l) : Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))ˣ) :
      Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))) =
    rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
    rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l) := by
  have e : (tw M H 1).g (p, k) (q, l) = (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l ^ (-(1 : ℤ))))⁻¹ :
        Γ(X, M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l))ˣ) := rfl
  rw [e, map_zpow, zpow_neg, zpow_one, inv_inv]
  rfl

def prodSec (u : LB.Sec M) (s : LB.Sec H) : LB.Sec (tw M H 1) where
  f := fun pk => rs X (inf_le_left : M.U pk.1 ⊓ H.U pk.2 ≤ M.U pk.1) (u.f pk.1) *
    rs X (inf_le_right : M.U pk.1 ⊓ H.U pk.2 ≤ H.U pk.2) (s.f pk.2)
  compat := fun pk ql => by
    have key : ∀ (p q : M.ι) (k l : H.ι),
        rs X (inf_le_left : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ H.U k)
          (rs X inf_le_left (u.f p) * rs X inf_le_right (s.f k)) =
        (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
         rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l)) *
        rs X (inf_le_right : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U q ⊓ H.U l)
          (rs X inf_le_left (u.f q) * rs X inf_le_right (s.f l)) := by
      intro p q k l
      have hu := congrArg (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q)) (u.compat p q)
      have hs := congrArg (rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l)) (s.compat k l)
      simp only [rs_rs, map_mul] at hu hs ⊢
      rw [hu, hs]
      ring
    exact (key pk.1 ql.1 pk.2 ql.2).trans (congrArg (· * _) (tw_one_g (M := M) (H := H) pk.1 ql.1 pk.2 ql.2).symm)

theorem nonzeroLocus_prodSec (u : LB.Sec M) (s : LB.Sec H) :
    nonzeroLocus (prodSec u s) = nonzeroLocus u ⊓ nonzeroLocus s := by
  have hb : ∀ (p : M.ι) (k : H.ι), X.basicOpen ((prodSec u s).f ((p, k) : (tw M H 1).ι)) =
      X.basicOpen (u.f p) ⊓ X.basicOpen (s.f k) := by
    intro p k
    change X.basicOpen (rs X (inf_le_left : M.U p ⊓ H.U k ≤ M.U p) (u.f p) *
      rs X (inf_le_right : M.U p ⊓ H.U k ≤ H.U k) (s.f k)) = _
    rw [Scheme.basicOpen_mul]
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res]
    refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
      (le_inf (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _)) ((inf_le_right).trans (X.basicOpen_le _)))
        inf_le_left) (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _))
          ((inf_le_right).trans (X.basicOpen_le _))) inf_le_right))
  refine le_antisymm (iSup_le fun pk => ?_) ?_
  · exact (hb pk.1 pk.2).le.trans (inf_le_inf (le_iSup (fun k => X.basicOpen (u.f k)) pk.1)
      (le_iSup (fun k => X.basicOpen (s.f k)) pk.2))
  · change (⨆ p, X.basicOpen (u.f p)) ⊓ (⨆ k, X.basicOpen (s.f k)) ≤ _
    rw [iSup_inf_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    exact iSup_le fun k => (hb p k).ge.trans
      (le_iSup (fun pk => X.basicOpen ((prodSec u s).f pk)) ((p, k) : (tw M H 1).ι))

theorem eval₂Hom_ratios_surjective (hM : M.IsLB) {m : ℕ} (u : Fin (m + 1) → LB.Sec M)
    (hu : ⨆ b, nonzeroLocus (u b) = ⊤) (a : Fin (m + 1)) {D N : X.Opens} (hD : IsAffineOpen D)
    (hN : N = nonzeroLocus (u a) ⊓ D) (ρ : Fin (m + 1) → Γ(X, N))
    (hρ : ∀ c q, rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u c).f q) =
      rs X (inf_le_left : N ⊓ M.U q ≤ N) (ρ c) * rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u a).f q)) :
    Function.Surjective (MvPolynomial.eval₂Hom (rs X (hN.le.trans inf_le_right : N ≤ D)) ρ) := by
  subst hN
  have hVD : nonzeroLocus (u a) ⊓ D ≤ D := inf_le_right
  have hV : IsAffineOpen (nonzeroLocus (u a) ⊓ D) := GlobalTheory.isAffineOpen_nonzeroLocus_inf hM (u a) hD
  letI : Algebra Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) := (rs X hVD).toAlgebra
  intro x
  suffices hx : x ∈ Algebra.adjoin Γ(X, D) (Set.range ρ) by
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  let T : Set Γ(X, D) := {t | ∃ b p, X.basicOpen t ≤ X.basicOpen ((u b).f p)}
  have hT : Ideal.span T = ⊤ := by
    rw [← hD.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ y))
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hb
    obtain ⟨t, ht, hyt⟩ := hD.exists_basicOpen_le ⟨y, hp⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, b, p, ht⟩, hyt⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (Algebra.adjoin Γ(X, D) (Set.range ρ)).toSubmodule T hT x ?_
  rintro ⟨t, b, p, ht⟩
  have hWD : X.basicOpen t ≤ D := X.basicOpen_le t
  have hWp : X.basicOpen t ≤ M.U p := ht.trans (X.basicOpen_le _)
  have hW : IsAffineOpen (X.basicOpen t) := hD.basicOpen t
  let α : Γ(X, X.basicOpen t) := rs X hWp ((u a).f p)
  let β : Γ(X, X.basicOpen t) := rs X hWp ((u b).f p)
  have hβ : IsUnit β := by
    have h0 : IsUnit (rs X (X.basicOpen_le ((u b).f p)) ((u b).f p)) :=
      X.toRingedSpace.isUnit_res_basicOpen _
    have h1 := h0.map (rs X ht)
    rwa [rs_rs] at h1
  have hW'W : X.basicOpen α ≤ X.basicOpen t := X.basicOpen_le α
  have hW'eq : X.basicOpen α = X.basicOpen t ⊓ X.basicOpen ((u a).f p) := Scheme.basicOpen_res _ _ _
  have hW'V : X.basicOpen α ≤ nonzeroLocus (u a) ⊓ D := by
    rw [hW'eq]
    exact le_inf (inf_le_right.trans (GlobalTheory.basicOpen_le_nonzeroLocus _ _)) (inf_le_left.trans hWD)
  have hOW' : X.basicOpen (rs X hVD t) ≤ X.basicOpen α := by
    have e0 : X.basicOpen (rs X hVD t) = (nonzeroLocus (u a) ⊓ D) ⊓ X.basicOpen t :=
      Scheme.basicOpen_res _ _ _
    rw [e0, hW'eq]
    refine le_inf inf_le_right ?_
    rw [← GlobalTheory.nonzeroLocus_inf_chart]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hWp)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (X.basicOpen t)
    hW.isCompact hW.isQuasiSeparated α (rs X hW'V x)
  obtain ⟨k, z, hz⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t y
  obtain ⟨k', z', hz'⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t))
  change rs X hW'W y = (rs X hW'W α) ^ n * rs X hW'V x at hy
  change rs X hWD z = (rs X hWD t) ^ k * y at hz
  change rs X hWD z' = (rs X hWD t) ^ k' * ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) at hz'
  have hr := congrArg (rs X (le_inf hW'V (hW'W.trans hWp) : X.basicOpen α ≤ (nonzeroLocus (u a) ⊓ D) ⊓ M.U p))
    (hρ b p)
  simp only [map_mul, rs_rs] at hr
  set I : Γ(X, X.basicOpen t) := ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) with hIdef
  have hIβ : I * β = 1 := hβ.val_inv_mul
  have hz1 := congrArg (rs X hW'W) hz
  have hz1' := congrArg (rs X hW'W) hz'
  have hIβ' := congrArg (rs X hW'W) hIβ
  simp only [map_mul, map_pow, map_one, rs_rs] at hz1 hz1' hIβ'
  have hα : rs X hW'W α = rs X (hW'W.trans hWp) ((u a).f p) := rs_rs _ _ _
  have hβ' : rs X hW'W β = rs X (hW'W.trans hWp) ((u b).f p) := rs_rs _ _ _
  let c : Γ(X, D) := z * z' ^ n
  have e1 : rs X hW'V ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) = 0 := by
    simp only [c, map_sub, map_mul, map_pow, rs_rs]
    rw [hz1, hz1', hy]
    have hARI : rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I = 1 := by
      rw [hα, mul_comm (rs X _ ((u a).f p)), ← hr, ← hβ', mul_comm, hIβ']
    calc _ = rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x -
          rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x *
            (rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I) ^ n := by ring
      _ = 0 := by rw [hARI, one_pow, mul_one, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV.isCompact
    ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) (rs X hVD t) (by
      change rs X (X.basicOpen_le _) _ = 0
      rw [← rs_rs hW'V hOW', e1, map_zero])
  refine ⟨l + (k + n * k'), ?_⟩
  rw [Subalgebra.mem_toSubmodule, Algebra.smul_def]
  have e2 : algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x =
      algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ l * c) * ρ b ^ n := by
    change rs X hVD (t ^ (l + (k + n * k'))) * x = rs X hVD (t ^ l * c) * ρ b ^ n
    rw [mul_sub, sub_eq_zero] at hl
    rw [map_pow, map_mul, map_pow, pow_add, mul_assoc, hl, mul_assoc]
  change algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x ∈ _
  rw [e2]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _)

theorem veryAmpleBy_tw_of_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  intro R _ X f H M n m s u hH hM hs hu
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨m * n + m + n, fun j => prodSec (u (e j).1) (s (e j).2), ?_, fun j => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ a, nonzeroLocus (u a) by rw [hu]; trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (a, i), ?_⟩
    rw [nonzeroLocus_prodSec, e.apply_symm_apply]
    exact ⟨ha, hi⟩
  obtain ⟨aff, r, hr, sj⟩ := hs.2 (e j).2
  have loc := nonzeroLocus_prodSec (u (e j).1) (s (e j).2)
  have hNE := loc.le.trans inf_le_left
  have hND := loc.le.trans inf_le_right
  have o : r (e j).2 = 1 := Segre.ratio_self _ _ (hr _)
  choose ρ₀ hρ₀ using fun c => GlobalTheory.AmpleSpan.exists_isRatio (u c) (u (e j).1)
  have o' : ρ₀ (e j).1 = 1 := Segre.ratio_self _ _ (hρ₀ _)
  refine ⟨?_, fun b => rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2), fun b kk => ?_, ?_⟩
  · rw [loc]
    exact GlobalTheory.isAffineOpen_nonzeroLocus_inf hM _ aff
  · have h1 : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U kk.1 ≤ M.U kk.1) ((u (e b).1).f kk.1) =
        rs X inf_le_left (ρ₀ (e b).1) * rs X inf_le_right ((u (e j).1).f kk.1) := hρ₀ _ _
    have h2 := hr (e b).2 kk.2
    have hk1 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (u (e j).1) ⊓ M.U kk.1 :=
      le_inf (inf_le_left.trans hNE) (inf_le_right.trans inf_le_left)
    have hk2 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (s (e j).2) ⊓ H.U kk.2 :=
      le_inf (inf_le_left.trans hND) (inf_le_right.trans inf_le_right)
    replace h1 := congrArg (rs X hk1) h1
    replace h2 := congrArg (rs X hk2) h2
    simp only [map_mul, rs_rs] at h1 h2
    change rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e b).1).f kk.1) * rs X inf_le_right ((s (e b).2).f kk.2)) =
      rs X (inf_le_left : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)))
        (rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2)) *
      rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e j).1).f kk.1) * rs X inf_le_right ((s (e j).2).f kk.2))
    simp only [map_mul, rs_rs]
    rw [h1, h2]
    ring
  · have hgen := eval₂Hom_ratios_surjective hM u hu (e j).1 aff loc (fun c => rs X hNE (ρ₀ c))
      (fun c q => by
        have h : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U q ≤ M.U q) ((u c).f q) =
            rs X inf_le_left (ρ₀ c) * rs X inf_le_right ((u (e j).1).f q) := hρ₀ c q
        have h' := congrArg (rs X (le_inf (inf_le_left.trans hNE) inf_le_right :
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ M.U q ≤ nonzeroLocus (u (e j).1) ⊓ M.U q)) h
        simp only [map_mul, rs_rs] at h' ⊢
        exact h')
    rw [← RingHom.range_eq_top, eq_top_iff]
    rintro x -
    obtain ⟨P, rfl⟩ := hgen x
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨F, rfl⟩ := sj c
      induction F using MvPolynomial.induction_on with
      | C c₀ =>
        refine ⟨MvPolynomial.C c₀, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        simp only [AbLaw.cst, RingHom.comp_apply, rs_rs]
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F l hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e j).1, l)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o', map_one, _root_.one_mul]
    | add P Q hP hQ => rw [map_add (f := _)]; exact Subring.add_mem _ hP hQ
    | mul_X P c hP =>
      rw [map_mul]
      refine Subring.mul_mem _ hP ⟨MvPolynomial.X (e.symm (c, (e j).2)), ?_⟩
      simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o, map_one, _root_.mul_one]
end GlobalTheory.GenTwist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmpleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  first | exact @GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | exact GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | (intros; apply GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConsecutiveVeryAmplePowersRelAmple

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem units_identity {G : Type*} [CommGroup G] (u P Q R β γ ε : G) (d t : ℤ) :
    (u * P * β⁻¹) * (u * Q * γ⁻¹) ^ (d * t) * (u * R * ε⁻¹) ^ d =
      u ^ (d * (t + 1) + 1) * (β * (γ ^ d) ^ t * (ε ^ d) ^ (1 : ℤ))⁻¹ * (P * Q ^ (d * t) * R ^ d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem pw_pw {X : Scheme.{0}} (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  show (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

theorem lbIso_tw_tw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d t : ℤ) :
    LBIso (tw (tw L (pw L d) t) (pw L d) 1) (pw L (d * (t + 1) + 1)) := by
  refine GlobalTheory.LBAlg.lbIso_of_germs
    (A := tw (tw L (pw L d) t) (pw L d) 1) (B := pw L (d * (t + 1) + 1))
    (fun p => res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.1 from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g p.1 p.2.1.1) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.2 from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g p.1 p.2.1.2) ^ (d * t) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.2 from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g p.1 p.2.2) ^ d) ?_
  rintro x ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩ ha hp ha' hq
  have hb : x ∈ L.U b := hp.1.1
  have hc : x ∈ L.U c := hp.1.2
  have he : x ∈ L.U e := hp.2
  have hb' : x ∈ L.U b' := hq.1.1
  have hc' : x ∈ L.U c' := hq.1.2
  have he' : x ∈ L.U e' := hq.2
  have inv : ∀ {j j' : L.ι}, x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U j' ⊓ L.U j) (L.g j' j) = (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ :=
    fun hj hj' => eq_inv_of_mul_eq_one_right
      ((gm_cocycle hL (𝟙 X) x hj hj' hj).trans (gm_self hL (𝟙 X) x hj))
  have rel : ∀ {i i' j j' : L.ι}, x ∈ L.U i → x ∈ L.U i' → x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) = gm (𝟙 X) x (L.U i ⊓ L.U i') (L.g i i') *
        gm (𝟙 X) x (L.U i' ⊓ L.U j') (L.g i' j') * (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ := by
    intro i i' j j' hi hi' hj hj'
    rw [← gm_cocycle hL (𝟙 X) x hi hi' hj, ← gm_cocycle hL (𝟙 X) x hi' hj' hj, inv hj hj', mul_assoc]
  have sec : ∀ (a₀ b₀ c₀ e₀ : L.ι) (h : (𝟙 X : X ⟶ X) x ∈ (pw L (d * (t + 1) + 1)).U a₀ ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀)),
      gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀))
        (res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U b₀ from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g a₀ b₀) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U c₀ from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g a₀ c₀) ^ (d * t) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U e₀ from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g a₀ e₀) ^ d) =
      gm (𝟙 X) x (L.U a₀ ⊓ L.U b₀) (L.g a₀ b₀) * gm (𝟙 X) x (L.U a₀ ⊓ L.U c₀) (L.g a₀ c₀) ^ (d * t) *
        gm (𝟙 X) x (L.U a₀ ⊓ L.U e₀) (L.g a₀ e₀) ^ d := by
    intro a₀ b₀ c₀ e₀ h
    rw [map_mul, map_mul, map_zpow, map_zpow, gm_res _ x _ h, gm_res _ x _ h, gm_res _ x _ h]
  have eB : gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a ⊓ (pw L (d * (t + 1) + 1)).U a')
      ((pw L (d * (t + 1) + 1)).g a a') = gm (𝟙 X) x (L.U a ⊓ L.U a') (L.g a a') ^ (d * (t + 1) + 1) :=
    map_zpow (gm (𝟙 X) x (L.U a ⊓ L.U a')) (L.g a a') _
  have eA : gm (𝟙 X) x ((tw (tw L (pw L d) t) (pw L d) 1).U ((b, c), e) ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b', c'), e'))
      ((tw (tw L (pw L d) t) (pw L d) 1).g ((b, c), e) ((b', c'), e')) =
      gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b') * (gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d) ^ t *
        (gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d) ^ (1 : ℤ) := by
    have g1 : gm (𝟙 X) x ((pw L d).U c ⊓ (pw L d).U c') ((pw L d).g c c') =
        gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d := map_zpow _ _ _
    have g2 : gm (𝟙 X) x ((pw L d).U e ⊓ (pw L d).U e') ((pw L d).g e e') =
        gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d := map_zpow _ _ _
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L d) t) (pw L d) 1 (𝟙 X) x ((b, c), e) ((b', c'), e') ⟨hp, hq⟩).trans ?_
    exact congrArg₂ (· * ·) ((GlobalTheory.LBAlg.gm_tw L (pw L d) t (𝟙 X) x (b, c) (b', c') ⟨hp.1, hq.1⟩).trans
      (congrArg₂ (· * ·) rfl (congrArg (· ^ t) g1))) (congrArg (· ^ (1 : ℤ)) g2)
  refine (sec a b c e ⟨ha, hp⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm
    (congrArg (·⁻¹) eA.symm)) (sec a' b' c' e' ⟨ha', hq⟩).symm))
  rw [rel ha ha' hb hb', rel ha ha' hc hc', rel ha ha' he he']
  exact units_identity _ _ _ _ _ _ _ d t

end GlobalTheory.FormalAlg.ConsecPowers

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem exists_veryAmpleBy_pw_and_succ : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  intro R _ X L hL hA
  obtain ⟨d₁, hd₁, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R X L hL).1 hA
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₁ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated R X.left X.hom _ n s hH hs L hL
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t₀ ≤ (t : ℤ) := ⟨t₀.toNat, Int.self_le_toNat t₀⟩
  obtain ⟨m, u, hu⟩ := ht₀ (t : ℤ) ht
  refine ⟨d₁ * (t + 1), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), fun c hc => ?_⟩
  rcases hc with rfl | rfl
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R X.left X.hom _ n s hH hs (t + 1) (by omega)
    have e : GlobalTheory.AbLaw.pw L ((d₁ * (t + 1) : ℕ) : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) ((t + 1 : ℕ) : ℤ) := by
      rw [pw_pw]
      push_cast
      rfl
    rw [e]
    exact ⟨n', s', hs'⟩
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple R X.left X.hom (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (tw L (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (t : ℤ))
      n m s u hH (isLB_tw hL hH _) hs hu
    obtain ⟨s'', hs''⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw (isLB_tw hL hH _) hH 1) (isLB_pw hL _)
      (lbIso_tw_tw hL (d₁ : ℤ) (t : ℤ)) hs'
    have e : ((d₁ * (t + 1) + 1 : ℕ) : ℤ) = (d₁ : ℤ) * ((t : ℤ) + 1) + 1 := by push_cast; ring
    rw [e]
    exact ⟨n', s'', hs''⟩

end GlobalTheory.FormalAlg.ConsecPowers
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConsecutiveVeryAmplePowersRelAmpleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_consecutive_veryAmple_powers_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  first | exact @GlobalTheory.FormalAlg.ConsecPowers.exists_veryAmpleBy_pw_and_succ | exact GlobalTheory.FormalAlg.ConsecPowers.exists_veryAmpleBy_pw_and_succ | (intros; apply GlobalTheory.FormalAlg.ConsecPowers.exists_veryAmpleBy_pw_and_succ <;> assumption)
end
end
