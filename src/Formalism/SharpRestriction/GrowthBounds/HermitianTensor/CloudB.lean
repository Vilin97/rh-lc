module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIsoDef
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamPolySmulRight
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ProdMemHten
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LastNeZero

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem last_ne_zero'' (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem lamAt_add' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X + Y) s = lamAt X s + lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply]
    ring

theorem lamAt_sub' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X - Y) s = lamAt X s - lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.sub_apply]
    ring

theorem lamAt_dualW {n' m : ℕ} (lo : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (dualW lo) s = dualWt (lamAt lo s) := by
  unfold lamAt dualW
  split_ifs <;> rfl

theorem dualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  simp only [dualWt]
  have := h (Fin.rev_le_rev.mpr hij)
  linarith

theorem flatW_top {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    flatW m al be s.val = wtPQ m (al s) (be s) := by
  funext i
  simp only [flatW, wtPQ, dif_pos s.2]

theorem flatW_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    flatW m al be s = 0 := by
  funext i
  simp only [flatW, dif_neg hs, Pi.zero_apply]

theorem flatW_add {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be al' be' : TT → ℕ) :
    flatW m (fun s => al s + al' s) (fun s => be s + be' s) = flatW m al be + flatW m al' be' := by
  funext s i
  simp only [flatW, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

theorem lo_apply (m : ℕ) (ccl P Q : ℕ) (lam : Fin (m + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last m) = -((Q : ℤ) + ccl)) (i : Fin (m + 1)) :
    (lam - wtPQ m P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last m then -(ccl : ℤ) else lam i := by
  simp only [Pi.sub_apply, wtPQ]
  split_ifs with h1 h2
  · subst h1
    rw [h0]
    ring
  · subst h2
    rw [hl]
    ring
  · ring

theorem bE_snd {K : Type} [Field K] {α : Type} (b : Bool) (f : MvPolynomial α K) :
    rename (Prod.snd : Bool × α → α) (rename (fun v => (b, v)) f) = f := by
  rw [rename_rename]
  exact congrArg (fun φ => φ f) rename_id

theorem posOK_zero {p n' : ℕ} (R : RS p n') (m : ℕ) : PosOK R m 0 0 0 0 0 0 1 0 := by
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hz := tn_nuOf_zero m

  let abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (rename (Prod.snd : Bool × (Fin (m + 1) × Fin (m + 1)) → Fin (m + 1) × Fin (m + 1))).toLinearMap
  have hLam : ∀ v t : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) = v * t := by
    intro v t
    simp only [abelian₂, AlgHom.toLinearMap_apply, map_mul, blockEmb, bE_snd]
  have hlat : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (c : R.Kf), IsUnit g.det → c ≠ 0 →
      IsLattice R.O (colSpan R.O (g * lb_D (m + 1) 1 c)) :=
    fun g c hg hc => ⟨_, by rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ c hc), rfl⟩
  have h1H : ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
      (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) ∈ H0 R.O m 0 Λ :=
    fun Λ hΛ => (invariant_sections_zero_weight_iff m Λ hΛ 1).mpr ⟨1, by simp⟩
  refine ⟨abelian₂, ?_, ?_, ?_⟩
  · intro v hv t ht
    rw [hLam]
    rw [hz] at hv ht ⊢
    rw [tn_const _ _ v hv, tn_const _ _ t ht, ← C_mul]
    exact tn_C_mem _ _ _
  · intro Λ hΛ v hv t ht
    rw [hLam]
    obtain ⟨a, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ v).mp hv
    obtain ⟨b, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ t).mp ht
    exact (invariant_sections_zero_weight_iff m Λ hΛ _).mpr ⟨a * b, by rw [map_mul, C_mul]⟩
  · intro g hg
    refine ⟨1, 1, fun _ => 1, fun _ => 1, fun _ => 0, by simp, fun _ => le_rfl, ?_, ?_⟩
    · intro a' b F _
      rw [hLam, Subsingleton.elim a' b]
      simp
    · intro c hc
      have hL := hlat g c hg hc
      simp only [Pi.zero_apply, zpow_zero, one_smul]
      refine ⟨h1H _ hL, ?_, fun _ => h1H _ hL, fun _ => h1H _ hL⟩
      rintro ⟨z', hz', he⟩
      obtain ⟨d, rfl⟩ := (invariant_sections_zero_weight_iff m _ hL z').mp hz'
      have h2 : (C (algebraMap R.O R.Kf 1) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) =
          C (algebraMap R.O R.Kf (R.w * d)) := by
        rw [map_one, map_one, map_mul, C_mul, tn_smulC]
        exact he
      have h3 := hinj (MvPolynomial.C_injective _ _ h2)
      exact R.std.2.1.not_isUnit (IsUnit.of_mul_eq_one _ h3.symm)

theorem posOK_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (a ccl P Q : ℕ)
    (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) (h8 : 2 * ccl ≤ 8 * a) :
    PosOK R (mm + 1) lam (wtPQ (mm + 1) P Q) (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))
      (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) (lam - wtPQ (mm + 1) P Q) (dualWt (lam - wtPQ (mm + 1) P Q))
      (weylDim mm (fun j => lam j.castSucc.succ)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨abelian₂, hA, hB, hC⟩ := h1 p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  refine ⟨abelian₂, hA, hB, fun g hg => ?_⟩
  obtain ⟨nb, z0, s, s', ka, e1, e2, e3, e4⟩ := hC g hg
  refine ⟨nb, z0, s, s', ka, e1, e2, e3, fun c hc => ?_⟩
  have hl0 := last_ne_zero'' (mm + 1) (by omega)
  have z1 : (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = ((2 * ccl : ℕ) : ℤ) := by simp [wtPQ]
  have z2 : (lam - wtPQ (mm + 1) P Q) 0 = ((ccl : ℕ) : ℤ) := by
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_pos rfl]
  have z3 : (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = ((ccl : ℕ) : ℤ) := by
    simp only [dualWt, Fin.rev_zero]
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_neg hl0, if_pos rfl, neg_neg]
  rw [z1, z2, z3, zpow_natCast, zpow_natCast]
  exact e4 c hc

theorem top_hyps {n' mm : ℕ} (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hBase : IsBaseWeight TT aw bw ccl lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (s : TT) :
    lam0 s.val 0 = (A s : ℤ) + ccl ∧ lam0 s.val (Fin.last (mm + 1)) = -((B s : ℤ) + ccl) ∧
      ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam0 s.val i| ≤ ccl := by
  obtain ⟨h0, hl, hm⟩ := (hBase s.val).1 s.2
  obtain ⟨hA, hB⟩ := hAB s
  exact ⟨by rw [h0]; linarith, by rw [hl]; linarith, hm⟩

theorem posOK_at_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (TT : Finset (Fin n'))
    (a ccl : ℕ) (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ)
    (hBase : IsBaseWeight TT aw bw ccl lam0) (hDom : IsDominant lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (h8 : 2 * ccl ≤ 8 * a) (s : TT) :
    PosOK R (mm + 1) (lamAt lam0 s.val) (lamAt (flatW (mm + 1) A B) s.val)
      (lamAt (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) s.val)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) s.val)
      (lamAt (lam0 - flatW (mm + 1) A B) s.val) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s.val)
      (weylDim mm (cloudAt lam0 s.val)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨t0, tl, tm⟩ := top_hyps TT ccl aw bw lam0 A B hBase hAB s
  have hl0 := last_ne_zero'' (mm + 1) (by omega)

  have hflat : ∀ al be : TT → ℕ, lamAt (flatW (mm + 1) al be) s.val =
      if Even s.val.val then wtPQ (mm + 1) (al s) (be s) else wtPQ (mm + 1) (be s) (al s) := by
    intro al be
    unfold lamAt
    split_ifs with he
    · exact flatW_top (mm + 1) al be s
    · funext i
      rw [flatW_top]
      simp only [wtPQ]
      by_cases hi0 : i = 0
      · subst hi0
        simp [Fin.rev_zero, hl0]
      · by_cases hil : i = Fin.last (mm + 1)
        · subst hil
          simp [Fin.rev_last, hl0]
        · have h1 : i.rev ≠ 0 := fun h => hil (by rw [← Fin.rev_rev i, h, Fin.rev_zero])
          have h2 : i.rev ≠ Fin.last (mm + 1) := fun h => hi0 (by rw [← Fin.rev_rev i, h, Fin.rev_last])
          simp [hi0, hil, h1, h2]
  rw [lamAt_sub', lamAt_dualW, lamAt_sub', hflat, hflat, hflat]
  rw [show cloudAt lam0 s.val = fun j => lamAt lam0 s.val j.castSucc.succ from rfl]
  by_cases he : Even s.val.val
  · simp only [if_pos he]
    have hlam' : lamAt lam0 s.val = lam0 s.val := by
      unfold lamAt
      rw [if_pos he]
    rw [hlam']
    exact posOK_top h1 R mm hmm a ccl (A s) (B s) (lam0 s.val) (hDom s.val) t0 tl tm h8
  · simp only [if_neg he]
    have hlam' : lamAt lam0 s.val = fun i => -lam0 s.val i.rev := by
      unfold lamAt
      rw [if_neg he]
    rw [hlam']
    refine posOK_top h1 R mm hmm a ccl (B s) (A s) _ (dualWt_anti _ (hDom s.val)) ?_ ?_ ?_ h8
    · simp only [Fin.rev_zero]
      rw [tl]
      try ring
    · simp only [Fin.rev_last]
      rw [t0]
      try ring
    · intro i hi1 hi2
      rw [abs_neg]
      refine tm i.rev ?_ ?_
      · rw [Fin.val_rev]
        omega
      · rw [Fin.val_rev]
        omega

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudB

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

private theorem sub_wtPQ_apply_eq_ite (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl)) (i : Fin (mm + 1 + 1)) :
    (lam - wtPQ (mm + 1) P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last (mm + 1) then -(ccl : ℤ) else lam i := by
  simp only [Pi.sub_apply, wtPQ]
  split_ifs with h1 h2
  · subst h1
    rw [h0]
    ring
  · subst h2
    rw [hl]
    ring
  · ring

private theorem antitone_sub_wtPQ (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam)
    (h0 : lam 0 = (P : ℤ) + ccl) (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) :
    Antitone (lam - wtPQ (mm + 1) P Q) := by
  intro a b hab
  rw [sub_wtPQ_apply_eq_ite mm ccl P Q lam h0 hl a, sub_wtPQ_apply_eq_ite mm ccl P Q lam h0 hl b]
  have hlv : (Fin.last (mm + 1)).val = mm + 1 := Fin.val_last _
  have hab' : a.val ≤ b.val := hab
  have hc : (0 : ℤ) ≤ (ccl : ℤ) := Int.natCast_nonneg _
  have hbl' := b.isLt
  have hal' := a.isLt
  by_cases ha0 : a = 0
  · subst ha0
    rw [ite_eq_left rfl]
    split_ifs with hb0 hbl
    · exact le_refl _
    · linarith
    · have hb1 : 0 < b.val := Nat.pos_of_ne_zero (fun h => hb0 (Fin.ext h))
      have hb2 : b.val < mm + 1 := by
        have : b.val ≠ mm + 1 := fun h => hbl (Fin.ext (h.trans hlv.symm))
        omega
      exact le_trans (le_abs_self _) (hmid b hb1 hb2)
  · by_cases hal : a = Fin.last (mm + 1)
    · have hb : b = Fin.last (mm + 1) := by
        apply Fin.ext
        rw [hal] at hab'
        omega
      subst hal
      subst hb
      exact le_refl _
    · have ha1 : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
      have ha2 : a.val < mm + 1 := by
        have : a.val ≠ mm + 1 := fun h => hal (Fin.ext (h.trans hlv.symm))
        omega
      rw [ite_eq_right ha0, ite_eq_right hal]
      split_ifs with hb0 hbl
      · exfalso
        have : b.val = 0 := by rw [hb0]; rfl
        omega
      · linarith [neg_abs_le (lam a), hmid a ha1 ha2]
      · exact hlam hab

theorem restCloudLat_of (h1 : CloudOne) (hCO : CartanOnto) (hIso : CloudIsoP) : RestCloudLat := by
  unfold RestCloudLat
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hbase hdom hoff hAB hc H Hp ze lo lo' hH hHp hze hlo hlo'
  subst hH hHp hze hlo hlo'
  have hdomlo : IsDominant (lam0 - flatW (mm + 1) A B) := by
    intro s
    by_cases hs : s ∈ TT
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s - wtPQ (mm + 1) (A ⟨s, hs⟩) (B ⟨s, hs⟩) := by
        rw [Pi.sub_apply, ← flatW_top (mm + 1) A B ⟨s, hs⟩]
      rw [e]
      obtain ⟨h0, hl, hmid⟩ := (hbase s).1 hs
      obtain ⟨hA, hB⟩ := hAB ⟨s, hs⟩
      exact antitone_sub_wtPQ mm ccl _ _ (lam0 s) (hdom s) (by rw [h0]; linarith) (by rw [hl]; linarith) hmid
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s := by
        rw [Pi.sub_apply, flatW_off (mm + 1) A B s hs, sub_zero]
      rw [e]
      exact hdom s
  have hdomlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := by
    intro s a' b' hab
    show -(lam0 - flatW (mm + 1) A B) s b'.rev ≤ -(lam0 - flatW (mm + 1) A B) s a'.rev
    exact neg_le_neg (hdomlo s (Fin.rev_le_rev.mpr hab))
  have hadd1 : ∀ s, lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s
      = lamAt (flatW (mm + 1) A B) s + lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s := by
    intro s
    rw [← lamAt_add']
    congr 1
    exact flatW_add (mm + 1) A B (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)
  have hadd2 : ∀ s, lamAt lam0 s = lamAt (flatW (mm + 1) A B) s + lamAt (lam0 - flatW (mm + 1) A B) s := by
    intro s
    rw [lamAt_sub']
    ring
  have hdz : dualWt (0 : Fin (mm + 1 + 1) → ℤ) = 0 := by
    funext i
    simp [dualWt]
  have hpos : ∀ s, PosOK R (mm + 1) (lamAt lam0 s) (lamAt (flatW (mm + 1) A B) s)
      (lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s)
      (lamAt (lam0 - flatW (mm + 1) A B) s) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s)
      (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1) (if s ∈ TT then ⌈kappaOneExponent p a (mm + 1)⌉₊ else 0) := by
    intro s
    by_cases hs : s ∈ TT
    · rw [ite_eq_left hs, ite_eq_left hs]
      exact posOK_at_top h1 R mm hmm TT a ccl aw bw lam0 A B hbase hdom hAB hc ⟨s, hs⟩
    · rw [ite_eq_right hs, ite_eq_right hs, lamAt_dualW, lamAt_sub', tn_lamAt_zero lam0 s (hoff s hs),
        lamAt_flat_off (mm + 1) A B s hs,
        lamAt_flat_off (mm + 1) (fun s : TT => A s + 2 * ccl) (fun s : TT => B s + 2 * ccl) s hs,
        lamAt_flat_off (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s hs, sub_self, hdz]
      exact posOK_zero R (mm + 1)
  obtain ⟨mH, mU, abelian₂, hlat, hrest⟩ := cloudTen R (mm + 1) lam0 _ _ _ _ _ hdom (flatW_dom _ _ _)
    (flatW_dom _ _ _) (flatW_dom _ _ _) hdomlo hdomlo' hadd1 hadd2 _ _ hpos hCO hIso
  refine ⟨mH, mU, abelian₂, hlat, fun gs hgs => ?_⟩
  obtain ⟨nb, z0, sb, sb', ka, hnb, hka, hrest2⟩ := hrest gs hgs
  refine ⟨nb, z0, sb, sb', ka, ?_, ?_, hrest2⟩
  · have e : (∏ s : Fin n', (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1))
        = ∏ s : TT, weylDim mm (cloudAt lam0 ↑s) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_coe_sort TT (fun s => weylDim mm (cloudAt lam0 s))]
    rw [dimCl, ← e, ← hnb]
    exact (Rat.cast_natCast nb).symm
  · intro b
    have hb := hka b
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at hb
    exact hb

end Formalism.MainNotions.flipOneThree.Pf

end
end
end
