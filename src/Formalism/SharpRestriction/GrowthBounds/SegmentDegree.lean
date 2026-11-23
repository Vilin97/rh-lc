module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Coarse
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestCountOf
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SelIsComplRestrictSupport
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FiniteRestrictSupport
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DivMulSubLeDivSubDiv
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BetaRatioBound
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightAlt
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestLamOfRests
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamMZero
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.M0LeBwOfIsW
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumPosOfPer
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamImgApply
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamSatRestrict

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_sat_restrict {O σ : Type} [CommRing O] [IsDomain O] (s : Set (σ →₀ ℕ)) (f : MvPolynomial σ O) (a : O)
    (ha : a ≠ 0) (h : a • f ∈ restrictSupport O s) : f ∈ restrictSupport O s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  intro m hm
  apply h
  have hm' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm)
  refine Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact mul_ne_zero ha hm'

theorem lam_dvd_of_res {O σ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (P : MvPolynomial σ O) (h : MvPolynomial.map (IsLocalRing.residue O) P = 0) :
    ∃ z : MvPolynomial σ O, P = ϖ • z := by
  have hd : C ϖ ∣ P := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (AddMonoidAlgebra.coeff P m) = 0 := by
      rw [← MvPolynomial.coeff_map, h]
      simp
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨z, hz⟩ := hd
  exact ⟨z, by rw [hz, smul_eq_C_mul]⟩

theorem restLamA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestLamA := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX j b hb
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hsatX := (h12 p O Sd n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hNK
    (fun _ => by positivity)).2.2.1
  have hsat : ∀ (f : SegRing O r K) (a : O), a ≠ 0 → a • f ∈ X.Mj p K O j b → f ∈ X.Mj p K O j b := by
    intro f a ha h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨hsatX f a ha h1, lam_sat_restrict _ f a ha h2⟩, lam_sat_restrict _ f a ha h3⟩
  have hfin : Module.Finite O (X.Mj p K O j b) := restFin p n' r K X O j b hb
  have hfree : Module.Free O (X.Mj p K O j b) := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis O (X.Mj p K O j b)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨fun i => (bs i : SegRing O r K), fun i => (bs i).2, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro cb hcb i
  choose c hc using fun i => IsLocalRing.residue_surjective (cb i)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • (bs i : SegRing O r K)) = 0 := by
    rw [sel_red_sum, ← hcb]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  obtain ⟨z, hz⟩ := lam_dvd_of_res hϖ _ h1
  have hzM : z ∈ X.Mj p K O j b := by
    refine hsat z ϖ hϖ.ne_zero ?_
    rw [← hz]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bs i).2
  have h2 : ∑ i, c i • bs i = ϖ • (⟨z, hzM⟩ : X.Mj p K O j b) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hz
  have h3 := congrArg (fun v => bs.repr v i) h2
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
  rw [← hc i, h3, map_mul]
  have : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  rw [this, zero_mul]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestLamOf

section

@[expose] public section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem restLam_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hDeg : RestLamDeg C₀) : RestLam C₀ :=
  restLam_of_rests C₀ (restLamA_of D hAdm) (restLamInj C₀) hDeg

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BfamAtWLetterEq

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section LD

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

omit [NeZero n'] [NeZero r] in
theorem lamd_eZ_per (e : Fin X.F.J → Fin r → ℕ) (j m : ℤ) : X.eZ e (j + m * X.F.J) = X.eZ e j := by
  unfold Dat.eZ
  split_ifs with h
  · congr 1
    ext
    simp
  · rfl

theorem lamd_nz_per {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (la : Fin n' → Fin (r + K) → ℕ) (j x m : ℤ) :
    X.nz p K la (j + m * X.F.J) (x + m * n') = X.nz p K la j x := by
  unfold Dat.nz
  have hpos : posOf n' (x + m * (n' : ℤ)) = posOf n' x := by
    ext
    simp [posOf]
  rw [hpos, sum_Pz_per X p K hV j x m]

theorem bfam_at_w_letter_eq {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (la : Fin n' → Fin (r + K) → ℕ)
    (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) (i : ℕ) (hi : i < r) :
    X.bfam p K la e j (X.F.fr (j - 1) i) =
      (X.nz p K la (j - 1) (X.F.fr (j - 1) i) - X.eZ e (j - 1) ⟨i, hi⟩) / X.Qc p K (j - 1) := by
  have hmono : ∀ (k : ℤ) (a b : ℕ), a < b → b < r → X.F.fr k a < X.F.fr k b := by
    intro k a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
      · exact lt_trans (ih h (by omega)) (hV.2.2.1 k b (by omega))
      · subst h
        exact hV.2.2.1 k a (by omega)
  have hle0 : X.F.fr (j - 1) 0 ≤ X.F.fr (j - 1) i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]
    · exact (hmono _ 0 i h hi).le
  have hleR : X.F.fr (j - 1) i ≤ X.F.fr (j - 1) (r - 1) := by
    rcases eq_or_lt_of_le (Nat.le_pred_of_lt hi) with h | h
    · rw [h]
      exact le_rfl
    · exact (hmono _ i (r - 1) h (by omega)).le
  have hlt : X.F.fr (j - 1) (r - 1) < X.F.fr j 0 := by
    have h := hV.2.2.2.1 (j - 1)
    simp only [sub_add_cancel] at h
    exact h
  have hle2 : X.F.fr j 0 ≤ X.F.fr j (r - 1) := by
    rcases Nat.eq_zero_or_pos (r - 1) with h | h
    · rw [h]
    · exact (hmono j 0 (r - 1) h (by omega)).le
  have hmem : X.F.fr (j - 1) i ∈ X.F.letters j := by
    unfold Formalism.MainNotions.G.Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hle0, by linarith⟩, (hV.2.2.2.2.1 (j - 1) i hi).1⟩
  have hW : X.F.IsW j (X.F.fr (j - 1) i) := hleR
  unfold Dat.bfam
  rw [if_pos hmem, if_pos hW, Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact absurd h (ne_of_gt (hmono _ _ _ h' hi))
    · exact absurd h (ne_of_lt (hmono _ _ _ h' b.isLt))
  · simp

end LD

theorem lamd_Bw_pos {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r} (hX : X.Hyp p K)
    (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (j y : ℤ) (hy : y ∈ X.F.letters j) : 1 ≤ X.Bw p K j y := by
  have h := sum_aP hX hLa hk j y hy
  have hp := hX.prime.pos
  have hPpos : 0 < p ^ (X.F.dist j y + X.Rj p K j) := pow_pos hp _
  have hNs : (1 : ℝ) ≤ (X.Ns : ℝ) := by
    have h1 : 0 < (X.F.letters j).card := Finset.card_pos.mpr ⟨y, hy⟩
    have h2 := hX.card j
    exact_mod_cast (show 1 ≤ X.Ns by omega)
  have hY := hX.Y1
  have hr := hX.r2
  have hYN : (1 : ℝ) ≤ X.Y * (X.Ns : ℝ) := by nlinarith
  have hk2 : ((r + K + r + 2 : ℕ) : ℝ) ≤ 36 / 5 * (Dat.k (r := r) K) ^ 2 := by
    unfold Dat.k
    push_cast
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    nlinarith
  have hPr : (0 : ℝ) < ((p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℝ) := by exact_mod_cast hPpos
  have hreal : ((r + K + r + 2 : ℕ) : ℝ) * ((p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℝ) ≤
      (X.a' p K (posOf n' y) : ℝ) := by
    have e1 : ((p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) := by
      push_cast; rfl
    rw [e1] at hPr ⊢
    have hk0 : (0 : ℝ) ≤ (Dat.k (r := r) K) ^ 2 := sq_nonneg _
    calc ((r + K + r + 2 : ℕ) : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j)
        ≤ 36 / 5 * (Dat.k (r := r) K) ^ 2 * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) :=
          mul_le_mul_of_nonneg_right hk2 hPr.le
      _ ≤ 36 / 5 * (Dat.k (r := r) K) ^ 2 * (X.Y * (X.Ns : ℝ)) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) := by
          have := mul_le_mul_of_nonneg_left hYN (by positivity : (0 : ℝ) ≤ 36 / 5 * (Dat.k (r := r) K) ^ 2)
          nlinarith
      _ = 36 / 5 * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j)) := by ring
      _ ≤ _ := h
  have hnat : (r + K + r + 2) * p ^ (X.F.dist j y + X.Rj p K j) ≤ X.a' p K (posOf n' y) := by
    exact_mod_cast hreal
  have hdiv : r + K + r + 2 ≤ X.a' p K (posOf n' y) / p ^ (X.F.dist j y + X.Rj p K j) :=
    (Nat.le_div_iff_mul_le hPpos).mpr hnat
  unfold Dat.Bw
  omega

theorem restLamDeg : RestLamDeg 1088 := by
  intro p n' r K _ _ _ X hX hLa hk la hla e he
  classical
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hG := restLamGeo 1088 p n' r K X hX hLa hk
  have hlaS : ∀ t, (∑ c, la t c ≤ X.a' p K t) ∧ ∀ j : ℤ, ∀ x ∈ X.toLate j, posOf n' x = t →
      (∀ c, la t c < X.Pz p K j x) ∧ (∑ c, la t c) % X.Pz p K j x = X.a' p K t % X.Pz p K j x := fun t =>
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hla t)).2
  refine ⟨?_, ?_⟩
  · intro j x hx hW c
    have := ((hlaS (posOf n' x)).2 j x (Finset.mem_filter.mpr ⟨hx, hW⟩) rfl).1 c
    simpa [Dat.lamL, Dat.Pz] using this
  · intro m hm t
    have hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm j).1
    have hdeg : ∀ j x, ∑ c, m j (x, c) = X.bfam p K la e (j.val : ℤ) x := fun j => (hm j).2.1
    have hsplit : ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) =
        ∑ c, la t c + ∑ c : Fin (r + K), (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finsupp.add_apply]
      simp [Dat.lamL]
    rw [hsplit]
    by_cases ht : t ∈ X.F.TT
    · obtain ⟨j0, x0, hx0, rfl⟩ := hG.EX t ht
      rw [Finset.sum_congr rfl fun c _ => lam_eval X p K hG m hok j0 x0 hx0 c, ← Finset.mul_sum,
        Finset.sum_add_distrib, hdeg j0 x0, ← Finset.mul_sum]
      have hWs : ∑ c, segmentWeightExponent X K m (posOf n' x0) c =
          ∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
            if posOf n' x = posOf n' x0 then X.bfam p K la e (j.val : ℤ) x else 0 := by
        unfold segmentWeightExponent
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : posOf n' x = posOf n' x0
        · simp only [h, if_true]
          exact hdeg j x
        · simp only [h, if_false, Finset.sum_const_zero]
      rw [hWs]
      obtain ⟨hl1, hl2, hl3, hl4⟩ := sum_late_mem hx0
      obtain ⟨hs1, hs2⟩ := hlaS (posOf n' x0)
      obtain ⟨-, hs3⟩ := hs2 (j0.val : ℤ) x0 hx0 rfl
      have hPnz : X.Pz p K (j0.val : ℤ) x0 * X.nz p K la (j0.val : ℤ) x0 =
          X.a' p K (posOf n' x0) - ∑ c, la (posOf n' x0) c := by
        unfold Dat.nz
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hs3.symm))
      have hkey : X.bfam p K la e (j0.val : ℤ) x0 + X.Qc p K (j0.val : ℤ) *
          (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
            if posOf n' x = posOf n' x0 then X.bfam p K la e (j.val : ℤ) x else 0) =
          X.nz p K la (j0.val : ℤ) x0 := by
        by_cases h0 : X.F.fr (j0.val : ℤ) 0 ≤ x0
        · obtain ⟨i0, hi0, rfl⟩ := comb_frame_top X.F hV (j0.val : ℤ) x0 hl4 h0 (r - 1) (by omega) hl3
          obtain ⟨j1, mm, hj1⟩ : ∃ (j1 : Fin X.F.J) (mm : ℤ),
              (j1.val : ℤ) - 1 = (j0.val : ℤ) + mm * (X.F.J : ℤ) := by
            have hj0 := j0.isLt
            by_cases h : j0.val + 1 < X.F.J
            · exact ⟨⟨j0.val + 1, h⟩, 0, by push_cast; ring⟩
            · refine ⟨⟨0, by omega⟩, -1, ?_⟩
              have hJ' : (X.F.J : ℤ) = (j0.val : ℤ) + 1 := by
                have : X.F.J = j0.val + 1 := by omega
                exact_mod_cast this
              push_cast
              rw [hJ']; ring
          have hx1eq : X.F.fr ((j1.val : ℤ) - 1) i0 = X.F.fr (j0.val : ℤ) i0 + mm * n' := by
            rw [hj1]; exact fr_add_mul_period hV (j0.val : ℤ) i0 mm
          have hx1l : X.F.fr ((j1.val : ℤ) - 1) i0 ∈ X.F.letters (j1.val : ℤ) := TE.frp_mem hV (j1.val : ℤ) i0 hi0
          have hx1W : X.F.IsW (j1.val : ℤ) (X.F.fr ((j1.val : ℤ) - 1) i0) :=
            TE.fr_le hV ((j1.val : ℤ) - 1) i0 (r - 1) (by omega) (by omega)
          have hx1p : posOf n' (X.F.fr ((j1.val : ℤ) - 1) i0) = posOf n' (X.F.fr (j0.val : ℤ) i0) := by
            rw [hx1eq, sum_posOf_per]
          have hval : X.bfam p K la e (j1.val : ℤ) (X.F.fr ((j1.val : ℤ) - 1) i0) =
              (X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) - e j0 ⟨i0, hi0⟩) / X.Qc p K (j0.val : ℤ) := by
            rw [bfam_at_w_letter_eq X p K hV la e (j1.val : ℤ) i0 hi0, hx1eq, hj1, lamd_nz_per X p K hV, lamd_eZ_per,
              sum_Qc_per X p K hV, sum_eZ_val]
          have hsum : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
              if posOf n' x = posOf n' (X.F.fr (j0.val : ℤ) i0) then X.bfam p K la e (j.val : ℤ) x else 0) =
              X.bfam p K la e (j1.val : ℤ) (X.F.fr ((j1.val : ℤ) - 1) i0) := by
            rw [Finset.sum_eq_single j1]
            · rw [Finset.sum_eq_single (X.F.fr ((j1.val : ℤ) - 1) i0)]
              · rw [if_pos hx1p]
              · intro x hx hne
                obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
                rw [if_neg]
                intro h
                exact hne (hG.U2 j1 j1 x hxl hxW _ hx1l hx1W (h.trans hx1p.symm)).2
              · intro h
                exact absurd (Finset.mem_filter.mpr ⟨hx1l, hx1W⟩) h
            · intro j _ hne
              refine Finset.sum_eq_zero fun x hx => ?_
              obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
              rw [if_neg]
              intro h
              exact hne (hG.U2 j j1 x hxl hxW _ hx1l hx1W (h.trans hx1p.symm)).1
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hsum, hval, restLamTau p n' r K X hX la e j0 ⟨i0, hi0⟩]
          have hEE := (Finset.mem_filter.mp
            (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp he j0) ⟨i0, hi0⟩)).2
          have hpad := (restPad p n' r K X hX hLa hk la hla e he (j1.val : ℤ)).1 _ hx1l hx1W
          have hBw := lamd_Bw_pos hX hLa hk (j1.val : ℤ) _ hx1l
          rw [hval] at hpad
          have hpos : 1 ≤ (X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) - e j0 ⟨i0, hi0⟩) /
              X.Qc p K (j0.val : ℤ) := by
            have : (1 : ℤ) ≤ (((X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) - e j0 ⟨i0, hi0⟩) /
              X.Qc p K (j0.val : ℤ) : ℕ) : ℤ) := le_trans hBw hpad
            exact_mod_cast this
          have hle : e j0 ⟨i0, hi0⟩ ≤ X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) := by
            by_contra hlt
            have hz : X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) - e j0 ⟨i0, hi0⟩ = 0 := by omega
            rw [hz, Nat.zero_div] at hpos
            omega
          have hdvd : X.Qc p K (j0.val : ℤ) ∣
              X.nz p K la (j0.val : ℤ) (X.F.fr (j0.val : ℤ) i0) - e j0 ⟨i0, hi0⟩ :=
            Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hEE.symm)
          rw [Nat.mul_div_cancel' hdvd]
          omega
        · have hz : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
              if posOf n' x = posOf n' x0 then X.bfam p K la e (j.val : ℤ) x else 0) = 0 := by
            refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_
            obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
            rw [if_neg]
            intro h
            obtain ⟨⟨i, hi, hxi⟩, -⟩ := hG.LK j j0 x hxl hxW x0 hx0 h
            exact h0 (hxi ▸ fr_zero_le hV (j0.val : ℤ) i hi)
          rw [hz, mul_zero, add_zero]
          unfold Dat.bfam
          rw [if_pos hl1, if_neg hl2, if_neg h0]
      rw [hkey, hPnz]
      omega
    · have ha : X.a' p K t = 0 := by
        unfold Dat.a' Dat.d
        rw [if_neg ht]
        omega
      have h1 : ∑ c, la t c = 0 := by
        have := (hlaS t).1
        omega
      have h2 : ∑ c : Fin (r + K), (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [lam_img_apply X p K j (m j) (hok j) t c]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [if_neg]
        intro h
        exact ht (h ▸ (mem_letters_bounds hx).2.2)
      rw [h1, h2, ha]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree

section

@[expose] public section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (h41 : DiscriminantNonzeroModUniformiser) (h45 : AdmB D → GeneratorModuloUniformiser 1088)
    (hLam : AdmB D → RestLam 1088) (hPad : RestPad 1088) (hSum : RestSum 1088 1)
    (hMem : AdmB D → RestMem 1088) (hInd : AdmB D → RestInd 1088)
    (hT1 : AdmB D → GoodPathWeight 1088) (hMon : RestMon 1088) : SecondPartClosed D :=
  second_estimate_of_rank_bound D 1088 1 (by norm_num) (by norm_num) restDeg restSel fun hA =>
    restRank_of 1088 1 h41 (h45 hA)
      (restCount_of 1088 1 (hLam hA) (restSeg_of 1088 (hMem hA) (hInd hA) restFin (hT1 hA) hMon) hPad hSum)

theorem restMon : RestMon 1088 := restMon_of 1088 beta_ratio_bound tau_degree_on_path_bound residue_class_count

theorem restInd (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestInd 1088 := restInd_of 1088 (restKey_of D hAdm 1088)

theorem secondPartClosed (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  second_estimate_of_restrictions D discriminant_nonzero_mod_uniformiser (fun hA => generator_modulo_uniformiser_of_adm D hA 1088 (by norm_num))
    (fun hA => restLam_of D hA 1088 restLamDeg)
    restPad restSum (fun hA => restMem_of D hA) (fun hA => restInd D hA) (fun hA => good_path_weight D hA) restMon

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
