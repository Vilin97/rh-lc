module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbeddingStatement
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalRingCardinality.DataForced
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.BitVec
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.NotIsCsOfGIdx

section

@[expose] public section

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

theorem frobSet_ne' (D : D7) {p : ℕ} (hp : p.Prime) : ∃ g, g ∈ frobSet D p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have : IsGaloisGroup (D.host.E ≃ₐ[ℚ] D.host.E) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  obtain ⟨P, hP, hlo⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hpZ.ne_zero) P
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (D.host.E ≃ₐ[ℚ] D.host.E) P
  exact ⟨_, P, hP, hlo, σ, hσ, rfl⟩

theorem hEv_of_hNeZero {D : D7} {p : ℕ} (hp : p.Prime) (hN : HNeZero D.host p) : HEv D p := by
  obtain ⟨P, hP', hL, σ, hσ, hg⟩ := Classical.epsilon_spec (frobSet_ne' D hp)
  have h1 := @hN P hP' hL σ hσ
  rw [hg] at h1
  exact h1

end Formalism.MainNotions.G

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBounds

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwU.LowTerm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

variable {D : D7} {L : SizeData₂ D}

theorem sum_betaI (X : Inst D L) (K : Consts) (ce : ErrC) (j p : ℕ) (hs : ¬ IsSg D p) :
    ∑ r ∈ OrbitPlaces.repsPl X p, OrbitPlaces.betaI X K ce j p r =
      (∑ t ∈ reps X p, max (g0 X K (aL L) (bL L) p j t) 0) +
        ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have hd : Disjoint ((reps X p).image (fun t => ((false, t) : OrbitPlaces.Pl D)))
      ((reps X p).image (fun t => ((true, t) : OrbitPlaces.Pl D))) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t', -, h⟩ := Finset.mem_image.1 h2
    simp at h
  unfold OrbitPlaces.repsPl
  rw [if_neg hs, Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA, hs]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA]

theorem FInert_sub_EatI (X : Inst D L) (K : Consts) (ce : ErrC) {p j : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p)
    (hh : HEv D p) (hs : ¬ IsSg D p) (hj : j ∈ SizeData₂.lifts D) :
    FInert D j p - EatI L K ce j p ≤
      ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have h := OrbitPlaces.sumI X K ce p hp (Or.inl ⟨hc, hh⟩) j hj
  rw [sum_betaI X K ce j p hs] at h
  linarith

theorem sum_dG_le {m n : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (h0 : d 0 = 0) (hj : ∀ j, d j ≤ n) :
    ∑ j ∈ Finset.range m, (d j : ℝ) ≤ ((m : ℝ) - 1) * n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', h0]
  have : ∑ j ∈ Finset.range k, (d (j + 1) : ℝ) ≤ ∑ _j ∈ Finset.range k, (n : ℝ) :=
    Finset.sum_le_sum fun j _ => by exact_mod_cast hj _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast
  linarith

theorem lowS_le : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC)
    (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 →
    (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) →
    WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
      if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then
        FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) -
      ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  intro D u w hg L X K ce Xe dG hF h0 hd
  have hm : 1 ≤ D.R.m := le_trans one_le_two D.R.two_le_m
  have hloss := sum_dG_le hm h0 hd
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := by
    intro h
    have h' : D.host.cls (D.what₂.places.resChar w) = _ := h
    rw [hg.2.2.1] at h'
    exact absurd h' (by decide)
  have hev : HEv D (D.what₂.places.resChar w) := hEv_of_hNeZero hg.1 hg.2.2.2.1
  have hh := hev.ne_zero
  have hne : ∀ i : Fin 2, D.what₂.places.resChar w ≠ D.host.g i := fun i h => hg.2.2.2.2.1 (h ▸ D.host.g_level i)
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hg.2.2.1]; decide
  have h4 : D.what₂.places.resChar w ∉ L.gTypes := by simp [SizeData₂.gTypes, hne]
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by simp [SizeData₂.lifts]
  have hterm : ∀ j ∈ SizeData₂.lifts D, L.F j w - WeilJacquetShalikaLaw.ES L Xe K ce u j w =
      (if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) - WeilJacquetShalikaLaw.vDG D u w := by
    intro j hj
    rw [hF j hj w]
    unfold Fval FvalP WeilJacquetShalikaLaw.ES Eval WeilJacquetShalikaLaw.vDG
    simp only [if_neg (hne 0), if_neg (hne 1), if_neg (WeilJacquetShalikaLaw.residue_char_ne_level hg), if_neg h2, if_neg h4]
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · have hA : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n := ⟨Or.inl hc, hX⟩
      have hB : ¬ (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) := fun h => hh h.2
      simp only [if_pos hA, if_neg hB, if_pos hX]
      unfold FInert
      rw [if_neg hB]
      ring
    · have hA : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => hX h.2
      simp only [if_neg hA, if_neg hX]
      ring
  have hsum : WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w = (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) -
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := by
    unfold WeilJacquetShalikaLaw.lowS
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hl : SizeData₂.lifts D = Finset.Icc 1 D.R.m := rfl
    rw [hl]
    ring
  have hle : (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) ≤
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
        if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
          FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0 := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hX]
      exact FInert_sub_EatI X K ce hg.1 hc hev hs hj
    · simp [hX]
  have hv : ((D.R.m : ℝ) - 1) * (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) =
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := rfl
  rw [hsum]
  linarith

end GlobalTheory.TwU.LowTerm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBoundsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.low_term_le_second_real_place_bounds : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 → (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) → WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w), if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  first | exact @GlobalTheory.TwU.LowTerm.lowS_le | exact GlobalTheory.TwU.LowTerm.lowS_le | (intros; apply GlobalTheory.TwU.LowTerm.lowS_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlacesOffFirstOrbits

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.SecondOrbits

section Abstract

variable {V H : Type} [AddCommGroup H] [Finite H] {h : H} {bs : H → H}

omit [Finite H] in
theorem inv_nsmul {Z : Type} {f : H → Z} (hf : ∀ t, f (t + h) = f t) (t : H) (i : ℕ) : f (t + i • h) = f t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, hf, ih]

theorem exists_back (a : H) (i : ℕ) : ∃ k, k < addOrderOf h ∧ a + i • h + k • h = a := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  refine ⟨(i * (addOrderOf h - 1)) % addOrderOf h, Nat.mod_lt _ hpos, ?_⟩
  rw [mod_addOrderOf_nsmul, add_assoc, ← add_nsmul]
  have : i + i * (addOrderOf h - 1) = i * addOrderOf h := by
    obtain ⟨m, hm⟩ : ∃ m, addOrderOf h = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hm, Nat.add_sub_cancel]; ring
  rw [this, mul_comm, mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero, add_zero]

theorem second_orbits [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H] (n' : V → ℕ) (hn : ∀ v, n' v = addOrderOf h)
    (π : (Σ v, Fin (n' v)) ≃ Bool × H) (β : V → Bool) (r : V → H)
    (hπ : ∀ v s, π ⟨v, s⟩ = (β v, r v + s.val • h))
    (horb : ∀ t, ∃ i : ℕ, bs t + i • h = t) (hstep : ∀ t, bs (t + h) = bs t) (vOf : H → V)
    (hv : ∀ t0 ∈ Finset.univ.image bs, ∀ s, π ⟨vOf t0, s⟩ = (false, t0 + s.val • h)) :
    (∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true) ∧
      ∀ f : H → ℝ, (∀ t, f (t + h) = f t) →
        ∑ v ∈ Finset.univ \ (Finset.univ.image bs).image vOf, f (r v) = ∑ t ∈ Finset.univ.image bs, f t := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have reach : ∀ v, ∃ s, π ⟨v, s⟩ = (β v, bs (r v)) := fun v => by
    obtain ⟨i, hi⟩ := horb (r v)
    obtain ⟨k, hk, hk'⟩ := exists_back (h := h) (bs (r v)) i
    refine ⟨⟨k, by rw [hn]; exact hk⟩, ?_⟩
    rw [hπ]
    rw [hi] at hk'
    simp only [hk']
  have h1 : ∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true := fun v hvn => by
    by_contra hb
    have hb' : β v = false := by simpa using hb
    obtain ⟨s, hs⟩ := reach v
    have hm : bs (r v) ∈ Finset.univ.image bs := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h0 := hv _ hm ⟨0, by rw [hn]; exact hpos⟩
    simp only [zero_smul, add_zero] at h0
    rw [hb', ← h0] at hs
    have := congrArg Sigma.fst (π.injective hs)
    exact hvn (Finset.mem_image.2 ⟨_, hm, this.symm⟩)
  refine ⟨h1, fun f hf => ?_⟩
  refine Finset.sum_bij (fun v _ => bs (r v)) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
  · intro v hv1 v' hv2 he
    obtain ⟨s, hs⟩ := reach v
    obtain ⟨s', hs'⟩ := reach v'
    rw [h1 v (Finset.mem_sdiff.1 hv1).2] at hs
    rw [h1 v' (Finset.mem_sdiff.1 hv2).2] at hs'
    have he' : bs (r v) = bs (r v') := he
    rw [he', ← hs'] at hs
    exact congrArg Sigma.fst (π.injective hs)
  · intro t0 ht0
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 ht0
    obtain ⟨⟨v, s⟩, hvs⟩ := π.surjective (true, bs t)
    refine ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hm => ?_⟩, ?_⟩
    · obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 hm
      rw [hv t1 ht1] at hvs
      cases congrArg Prod.fst hvs
    · rw [hπ] at hvs
      have e1 : r v + s.val • h = bs t := congrArg Prod.snd hvs
      obtain ⟨i, hi⟩ := horb t
      show bs (r v) = bs t
      rw [← inv_nsmul hstep (r v) s.val, e1, ← inv_nsmul hstep (bs t) i, hi]
  · intro v _
    obtain ⟨i, hi⟩ := horb (r v)
    rw [← inv_nsmul hf (bs (r v)) i, hi]

end Abstract

open NumberField GlobalTheory.InertCompare

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (t : φ.A) : orderOf (φ.iota t) = addOrderOf t :=
  orderOf_ofAdd_eq_addOrderOf t

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem eq_tauPl (D : D7) {τ : D.what₂.Tau} {z : Bool × HH D} (h : ((D.eTau τ : D.R.Psi) : D.R.GG) = plGG D z) :
    τ = tauPl D z :=
  D.eTau.injective (Subtype.ext (h.trans (eTau_tauPl D z).symm))

theorem orbit_positions (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (v : Fin (D.gat u w hg).P.nV) :
    (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) ∧
      ∃ z : Bool × HH D, ∀ s : Fin ((D.gat u w hg).P.n' v),
        hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) z s.val) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := Or.inl hg.2.2.1
  have : (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.1.ne_zero)).2 (Nat.prime_iff_prime_int.1 hg.1)
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).nonempty_primesOver (S := 𝓞 D.host.E)
  obtain ⟨φ, hφ, hstep⟩ := exists_frob_step D _ hc P
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D _ hc
  have hn : (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) := by
    rw [hT.gat_n u w hg v P φ hφ, galE_frob_snd D _ h2 hq hd P φ hφ, orderOf_iotaH]
  have hpos : 0 < (D.gat u w hg).P.n' v := by rw [hn]; exact addOrderOf_pos _
  obtain ⟨z, hz⟩ := (tauPl_bijective D).2 (hT.gat_pos u w hg ⟨v, ⟨0, hpos⟩⟩)
  refine ⟨hn, z, ?_⟩
  rintro ⟨s, hs⟩
  induction s with
  | zero => rw [posPl_zero, hz]
  | succ s ih =>
    have hs' : s < (D.gat u w hg).P.n' v := Nat.lt_of_succ_lt hs
    have e1 : (⟨s + 1, hs⟩ : Fin ((D.gat u w hg).P.n' v)) = posAdd ⟨s, hs'⟩ 1 := Fin.ext (Nat.mod_eq_of_lt hs).symm
    refine eq_tauPl D ?_
    show _ = plGG D (posPl D _ z (s + 1))
    rw [e1, hT.gat_step u w hg v ⟨s, hs'⟩ P φ hφ, ih hs', eTau_tauPl, ← posPl_add, hstep]

theorem places_off_first_orbits : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → ∃ r : Fin (D.gat u w hg).P.nV → HH D, (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) ∧ (Y.Fl u w hg).TT v = ∅ ∧ ∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, r v) s.val)) ∧ ∀ f : HH D → ℝ, (∀ t, f (t + hP D (D.what₂.places.resChar w)) = f t) → ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), f (r v) = ∑ t ∈ reps X (D.what₂.places.resChar w), f t := by
  intro D u w hg L hT X Y hL
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun hs => by
    have := hg.2.2.1.symm.trans hs
    cases this
  have hstepP : stepP D (D.what₂.places.resChar w) = hP D (D.what₂.places.resChar w) := if_neg hs
  have hnP : nP D (D.what₂.places.resChar w) = addOrderOf (hP D (D.what₂.places.resChar w)) := if_neg hs
  have hpos : ∀ (z : Bool × HH D) (e : ℕ), posPl D (D.what₂.places.resChar w) z e =
      (z.1, z.2 + e • hP D (D.what₂.places.resChar w)) := fun z e => by
    simp [posPl, partner, hs]
  have hn := fun v => (orbit_positions D u w hg hT v).1
  choose z hz using fun v => (orbit_positions D u w hg hT v).2
  obtain ⟨-, -, -, -, -, hT2, hT1⟩ := hL u w hg
  have hreps : reps X (D.what₂.places.resChar w) = Finset.univ.image (X.bs (hP D (D.what₂.places.resChar w))) := by
    unfold reps
    rw [hstepP]
  have key := second_orbits (h := hP D (D.what₂.places.resChar w)) (bs := X.bs (hP D (D.what₂.places.resChar w)))
    (D.gat u w hg).P.n' hn ((hT.gat_pos u w hg).trans (plEquiv D).symm) (fun v => (z v).1) (fun v => (z v).2)
    (fun v s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq, hz, hpos]
      rfl)
    (X.bs_orb _) (X.bs_step _) (Y.vOf u w hg)
    (fun t0 ht0 s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq]
      exact eq_tauPl D ((hT1 t0 (hreps ▸ ht0)).2 s).1)
  rw [hreps]
  refine ⟨fun v => (z v).2, fun v hv => ?_, key.2⟩
  have hb : z v = (true, (z v).2) := Prod.ext (key.1 v hv) rfl
  refine ⟨(hn v).trans hnP.symm, ?_, fun s => by rw [hz, ← hb]⟩
  refine Finset.eq_empty_of_forall_notMem fun s => (hT2 v s ((z v).2 + s.val • hP D (D.what₂.places.resChar w)) ?_).1
  rw [hz, eTau_tauPl, hpos, hb]
  rfl

end GlobalTheory.SecondOrbits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.SiteSys

variable {D : D7}

theorem orbMap_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) (s : ZMod (nP D p)) :
    OrbitPlaces.orbMap D p (posPl D p r e) s = OrbitPlaces.orbMap D p r (s + (e : ZMod (nP D p))) := by
  unfold OrbitPlaces.orbMap
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p r s.val, posPl_mod, posPl_add, add_comm]

theorem topsOrb_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.topsOrb D p (posPl D p r e) = OrbitPlaces.topsOrb D p r := by
  unfold OrbitPlaces.topsOrb
  refine Finset.card_equiv (Equiv.addRight (e : ZMod (nP D p))) fun s => ?_
  simp [orbMap_posPl]

theorem errF_posPl {L : SizeData₂ D} (K : Consts) (ce : ErrC) (j p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.errF L K ce j p (posPl D p r e) = OrbitPlaces.errF L K ce j p r := by
  have h : ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p (posPl D p r e) s) =
      ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p r s) := by
    simp only [orbMap_posPl]
    exact Equiv.sum_comp (Equiv.addRight (e : ZMod (nP D p))) (fun s => wPl D j (OrbitPlaces.orbMap D p r s))
  unfold OrbitPlaces.errF
  rw [h, topsOrb_posPl]

theorem posPl_true_one {p : ℕ} (hs : ¬ IsSg D p) (t : HH D) : posPl D p (true, t) 1 = (true, t + hP D p) := by
  simp [posPl, partner, hs]

theorem notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem sysTw_sites : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  intro D L hT X Y K Dx lev Xe ce E LC hty hfa hF hadm hSh hCL hS hE μ hμ hT' hty' u w hg hQ
  obtain ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, h0, hj⟩ := hS μ hμ u w hg hQ
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.SecondOrbits.places_off_first_orbits D u w hg L hT X Y hty
  refine ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA,
    fun v j => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, r v) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, r v) else 0,
    ?_, ?_⟩
  · intro v hv j hjm
    obtain ⟨-, -, -, a2c, -, -, -, -, -, -, -, -, a11⟩ := hA
    by_cases hp : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hp]
      exact GlobalTheory.T.local_model_bound_place_over_second_embedding D u w hg L hT X Y K ce E hty hfa hadm hSh hCL hp _ _ std vp unif eO eO_spec dG dG_spec om Y5 a2c v (r v)
        (hr1 v hv).1 (hr1 v hv).2.2 j hjm
    · simp only [if_neg hp]
      exact a11 v j (lt_of_lt_of_eq hjm (hty u w hg).1.symm)
  · refine (GlobalTheory.T.low_term_le_second_real_place_bounds D u w hg L X K ce Xe dG hF h0 hj).trans (sub_le_sub_right (le_of_eq ?_) _)
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hr2 (fun t => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) ?_).symm
    intro t
    have h1 := posPl_true_one (notSg hg) t
    have h2 := FOrb_step D j (D.what₂.places.resChar w) (true, t) 1
    have h3 := errF_posPl (L := L) K ce j (D.what₂.places.resChar w) (true, t) 1
    rw [h1] at h2 h3
    simp only [h2, h3]

end GlobalTheory.TwU.SiteSys
end
end
