module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerTimesMonomial
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialMemSupported
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeS
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.PsiCutSupported
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentProductDegreeDetermined
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialMemSupported
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentProductDegreeDetermined
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialDegreeAtW

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_degAt_det {R : Type} [CommRing R] {n : ℕ} (y : Fin n → ℤ) (t : ℤ) :
    DegAt t (∑ a : Fin n, if y a = t then 1 else 0)
      (Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R))) := by
  classical
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin n => (MvPolynomial.X (y (σ i), i) : MvPolynomial (ℤ × Fin n) R))
    (fun i => if y (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (y (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if y a = t then 1 else 0)] at h2
  exact h2

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerMonomialDegree (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  X.m0 K * (∑ a : Fin r, if X.F.fr (j - 1) a.val = x then 1 else 0) +
    ∑ i : Fin r, ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat *
      (if X.F.fr (j - 1) i.val = x then 1 else 0)


omit [NeZero n'] [NeZero r] in
def memdMu (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) : ℕ :=
  ∑ v : Fin r × Fin r, u v * (if X.F.fr j v.1.val = x then 1 else 0)

end Dat

section Deg

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem degAt_disc_power_monomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (x : ℤ) :
    DegAt x (X.discPowerMonomialDegree p K j b x) (X.discPowerTimesMonomial p K O j b) := by
  classical
  unfold Dat.discPowerMonomialDegree Dat.discPowerTimesMonomial Dat.Dw
  refine degAt_mul (degAt_pow (mem_degAt_det _ x) _) ?_
  exact degAt_prod Finset.univ _ _ fun i _ => degAt_pow (degAt_X (x := x) (X.F.fr (j - 1) i.val, (0 : Fin r))) _

theorem mem_degAt_Mu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) :
    DegAt x (X.memdMu j u x) (X.memMu O j u) := by
  classical
  unfold Dat.memdMu Dat.memMu
  exact degAt_prod Finset.univ _ _ fun v _ => degAt_pow (degAt_X (x := x) (X.F.fr j v.1.val, v.2)) _

theorem disc_power_monomial_degree_off (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr (j - 1) a.val ≠ x) :
    X.discPowerMonomialDegree p K j b x = 0 := by
  unfold Dat.discPowerMonomialDegree
  simp [h]

theorem mem_dMu_off (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr j a.val ≠ x) :
    X.memdMu j u x = 0 := by
  unfold Dat.memdMu
  simp [h]

theorem disc_power_monomial_degree_at_w (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (a0 : Fin r) :
    X.discPowerMonomialDegree p K j b (X.F.fr (j - 1) a0.val) =
      X.m0 K + ((b (X.F.fr (j - 1) a0.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) a0.val)).toNat := by
  classical
  have hinj := fr_injective X.F hX.valid (j - 1)
  have hiff : ∀ a : Fin r, (X.F.fr (j - 1) a.val = X.F.fr (j - 1) a0.val) ↔ a = a0 :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.discPowerMonomialDegree
  simp only [hiff]
  simp

theorem mem_dMu_tau (hX : X.Hyp p K) (j : ℤ) (u : Fin r × Fin r → ℕ) (t : Fin r) :
    X.memdMu j u (X.F.fr j t.val) = ∑ c, u (t, c) := by
  classical
  have hinj := fr_injective X.F hX.valid j
  have hiff : ∀ a : Fin r, (X.F.fr j a.val = X.F.fr j t.val) ↔ a = t :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.memdMu
  rw [Fintype.sum_prod_type]
  simp only [hiff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mem_degAt_segRen_off {R : Type} [CommRing R] (j : ℤ) {n : ℕ} (A : MvPolynomial (Fin (segN X.F j) × Fin n) R)
    (x : ℤ) (hx : x ∉ X.F.letters j) : DegAt x 0 (segRen X.F j R n A) := by
  refine degAt_of_supported {v : ℤ × Fin n | v.1 ∈ X.F.letters j} ?_ ?_
  · refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact segE_mem X.F j u.1
  · intro v hv h
    exact hx (h ▸ hv)

end Deg

theorem restMemB_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemB C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q mm hmm x hx hW
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H : PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) :=
    plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hA : ¬ Even (segE X.F j i) → DegAt (segE X.F j i) (0 + 0 + b' i) (X.memA p K O j b q.1) := by
    intro ho
    unfold Dat.memA
    refine degAt_mul (degAt_mul ?_ ?_) (degAt_segRen X.F j u1 i)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (disc_power_monomial_mem_supported O j b _ fun a _ => hevW a) ?_
      intro v hv h
      exact ho (h ▸ hv)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (mem_Mu_supported O j _ _ fun a _ => hevT a) ?_
      intro v hv h
      exact ho (h ▸ hv)
  have hG : Even (segE X.F j i) → DegAt (segE X.F j i) (b'' i) (X.memG K O j q.1) := fun _ =>
    degAt_segRen X.F j u2 i
  rw [ordDeg_prod hA hG mm hmm]
  obtain ⟨-, gE, gO⟩ := hGood i hW
  split_ifs with he
  · have hs := (T.step_vec P2 i ((comb_vec X.F j i).mpr he)).2.2
    rw [h2] at hs
    have := gE he
    rw [hs] at this
    exact_mod_cast this
  · have hvec : (segLL X.F j).vec i = false := by
      by_contra h
      exact he ((comb_vec X.F j i).mp (by simpa using h))
    have hs := (T.step_cov P1 i hvec).2.2
    rw [h1] at hs
    have := gO he
    rw [hs] at this
    simpa using this

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.M0LeBwOfIsW

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section CD

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem m0_le_Bw_of_isW (hX : X.Hyp p K) (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (j : ℤ) (b : ℤ → ℕ)
    (hA : X.AdmLL p K j b) (x : ℤ) (hx : x ∈ X.F.letters j) (hW : X.F.IsW j x) : (X.m0 K : ℤ) ≤ X.Bw p K j x := by
  classical
  have hV := hX.valid
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have hlt : x < X.F.fr j 0 := by
    have h1 : x ≤ X.F.fr (j - 1) (r - 1) := hW
    have h2 := TE.fr_prev_lt hV j
    omega
  have hB := (TE.Bdeg_bounds hX hk h41 j b hA x hx hlt).1
  have hc := (TE.c_bounds hX h41 j x hx).1
  have B := basics hX
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hP : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by positivity
  have hc' : (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
      (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    rw [le_div_iff₀ hP]; exact hc
  have hk5 := B.k5
  have hN1 := B.Ns1
  have hY1 := B.Y1
  have hkN : 0 < Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
  have hbig : 2 * Dat.k (r := r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have h1 : (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
        (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
      have : 0 ≤ (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by positivity
      nlinarith
    have h2 : 2 * Dat.k (r := r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
      nlinarith
    linarith
  have hpos : (0 : ℝ) < (X.Bdeg p K j (X.restr j b) x : ℝ) := by linarith
  have hpos' : 0 < X.Bdeg p K j (X.restr j b) x := by exact_mod_cast hpos
  unfold Dat.Bdeg at hpos'
  rw [if_pos hW] at hpos'
  omega

theorem mem_degAt_ext {R : Type} [CommRing R] (j : ℤ) {n : ℕ} {bb : Fin (segN X.F j) → ℕ}
    {A : MvPolynomial (Fin (segN X.F j) × Fin n) R} (hA : A ∈ Pol R n bb) (x : ℤ) :
    DegAt x (Function.extend (segE X.F j) bb 0 x) (segRen X.F j R n A) := by
  by_cases hx : x ∈ X.F.letters j
  · obtain ⟨i, rfl⟩ := segE_surj X.F j hx
    rw [(segE_strictMono X.F j).injective.extend_apply]
    exact degAt_segRen X.F j hA i
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i, rfl⟩
      exact hx (segE_mem X.F j i))]
    exact mem_degAt_segRen_off j A x hx

theorem mem_restr_late (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (hx : x ∈ X.toLate j) : X.restr j b x = b x := by
  classical
  unfold Dat.restr
  rw [if_pos hx]

end CD

theorem restMemC_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestMemC 1088 := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H : PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) :=
    plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  have hA : X.memA p K O j b q.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x +
      Function.extend (segE X.F j) b' 0 x) :=
    mem_Pol_of_degAt fun x => degAt_mul (degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_Mu O j _ x))
      (mem_degAt_ext j u1 x)
  have hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0) :=
    mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x
  have hprod := hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)
  have hprev := TE.fr_prev_lt hV j
  have heq : ((fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x + Function.extend (segE X.F j) b' 0 x) +
      Function.extend (segE X.F j) b'' 0) = b := by
    funext x
    simp only [Pi.add_apply]
    by_cases hx : x ∈ X.F.letters j
    · obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      rw [(segE_strictMono X.F j).injective.extend_apply, (segE_strictMono X.F j).injective.extend_apply]
      have hs := hsum i
      have hrN := k_r_le_segN X.F hV hr j
      have hil := i.isLt
      by_cases hi1 : i.val < r
      ·
        have hxW := TE.dict_wE hV i hi1
        have hW : X.F.IsW j (segE X.F j i) := (TE.dict_w hV i).mpr hi1
        have hle : segE X.F j i ≤ X.F.fr (j - 1) (r - 1) := hW
        have hlt : segE X.F j i < X.F.fr j 0 := by omega
        have hdd := hPATH.degs i hlt
        unfold Dat.Bdeg at hdd
        rw [if_pos hW] at hdd
        have hm0 := m0_le_Bw_of_isW hX hLa hk j b hb.2.2 _ hx hW
        have hBw := hb.2.1 _ hx hW
        have e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = X.m0 K +
            ((b (segE X.F j i) : ℤ) - X.Bw p K j (segE X.F j i)).toNat := by
          have := disc_power_monomial_degree_at_w hX j b (⟨i.val, hi1⟩ : Fin r)
          simp only [] at this
          rw [← hxW] at this
          exact this
        have e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0 := mem_dMu_off j _ _ fun a => by
          have := kfr_le X.F hV j (Nat.zero_le a.val) a.isLt
          omega
        rw [e1, e2]
        omega
      · have hnW : ¬ X.F.IsW j (segE X.F j i) := fun h => hi1 ((TE.dict_w hV i).mp h)
        have hgt : X.F.fr (j - 1) (r - 1) < segE X.F j i := not_le.mp hnW
        have hlate : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hnW⟩
        have e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = 0 := disc_power_monomial_degree_off j b _ fun a => by
          have := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)
          omega
        by_cases hi2 : i.val < segN X.F j - r
        · have hlt := (segE_lt_fr_iff X.F hV hr j i).mpr hi2
          have hdd := hPATH.degs i hlt
          unfold Dat.Bdeg at hdd
          rw [if_neg hnW, mem_restr_late j b _ hlate] at hdd
          have e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0 := mem_dMu_off j _ _ fun a => by
            have := kfr_le X.F hV j (Nat.zero_le a.val) a.isLt
            omega
          rw [e1, e2]
          omega
        · have ht : i.val - (segN X.F j - r) < r := by omega
          have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
            (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
          have hdi := hd i ⟨i.val - (segN X.F j - r), ht⟩ hseg
          have e2 := mem_dMu_tau hX j q.1.2.2 (⟨i.val - (segN X.F j - r), ht⟩ : Fin r)
          simp only [] at e2 hdi
          rw [← hseg] at e2 hdi
          rw [mem_restr_late j b _ hlate] at hdi
          rw [e1, e2]
          omega
    · have hne : ¬ ∃ a, segE X.F j a = x := by
        rintro ⟨i, rfl⟩
        exact hx (segE_mem X.F j i)
      rw [Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne, hb.1 x hx,
        disc_power_monomial_degree_off j b x fun a h => hx (h ▸ TE.frp_mem hV j a.val a.isLt),
        mem_dMu_off j _ x fun a h => hx (h ▸ k_fr_mem_letters X.F hV j a.isLt)]
      rfl
  rw [heq] at hprod
  exact hprod

theorem restMemD_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemD C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H : PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) :=
    plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  have hA : X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x +
      Function.extend (segE X.F j) b' 0 x) :=
    mem_Pol_of_degAt fun x => degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_ext j u1 x)
  have hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0) :=
    mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x
  have hprod := hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)
  have hMu : plEmb O r K (X.memMu O j q.1.2.2) = monomial (X.monTau K j q.1.2.2) (1 : O) := by
    unfold Dat.memMu Dat.monTau
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  have hfac : plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) =
      monomial (X.monTau K j q.1.2.2) (1 : O) *
        (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1)) := by
    rw [← hMu]
    unfold Dat.memA
    simp only [map_mul]
    ring
  rw [hfac, MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm i hi c
  have hmm' : AddMonoidAlgebra.coeff (monomial (X.monTau K j q.1.2.2) (1 : O) *
      (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1))) mm ≠ 0 := by
    rw [← MvPolynomial.mem_support_iff]; exact_mod_cast hmm
  rw [MvPolynomial.coeff_monomial_mul'] at hmm'
  split_ifs at hmm' with hle
  · rw [one_mul] at hmm'
    have hsupp := MvPolynomial.mem_support_iff.mpr hmm'
    have hdeg := mem_Pol_iff.mp hprod _ hsupp (X.F.fr j i)
    have hrN := k_r_le_segN X.F hV hr j
    let idx : Fin (segN X.F j) := ⟨segN X.F j - r + i, by omega⟩
    have hidx : segE X.F j idx = X.F.fr j i := (segE_eq_fr_iff X.F hV j idx hi).mpr rfl
    have hprev := TE.fr_prev_lt hV j
    have e1 : X.discPowerMonomialDegree p K j b (X.F.fr j i) = 0 := disc_power_monomial_degree_off j b _ fun a => by
      have h3 := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)
      have h4 := kfr_le X.F hV j (Nat.zero_le i) hi
      omega
    simp only [Pi.add_apply] at hdeg
    rw [e1, ← hidx, (segE_strictMono X.F j).injective.extend_apply,
      (segE_strictMono X.F j).injective.extend_apply, hidx] at hdeg
    have h21 := tau_degree_on_path_bound p n' r K X hX j _ _ dd hPATH idx (by
      rw [hidx]; exact kfr_le X.F hV j (Nat.zero_le i) hi)
    have hs := hsum idx
    have hone : (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c) ≤
        multideg (mm - X.monTau K j q.1.2.2) (X.F.fr j i) := by
      unfold multideg
      exact Finset.single_le_sum (f := fun c' => (mm - X.monTau K j q.1.2.2) (X.F.fr j i, c'))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.castAdd K c))
    have hdec : mm (X.F.fr j i, Fin.castAdd K c) = X.monTau K j q.1.2.2 (X.F.fr j i, Fin.castAdd K c) +
        (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c) := by
      have := congrArg (fun f => f (X.F.fr j i, Fin.castAdd K c)) (add_tsub_cancel_of_le hle)
      simp only [Finsupp.add_apply] at this
      exact this.symm
    have hmt := monTau_apply X K hV j q.1.2.2 (⟨i, hi⟩ : Fin r) c
    simp only [] at hmt
    have huv := hu (⟨i, hi⟩, c)
    rw [hdec, hmt]
    omega
  · exact absurd rfl hmm'

theorem restMem_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestMem 1088 :=
  restMem_of_rests 1088 (restMemA_of D hAdm 1088) (restMemB_of D hAdm 1088) (restMemC_of D hAdm)
    (restMemD_of D hAdm 1088)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end
