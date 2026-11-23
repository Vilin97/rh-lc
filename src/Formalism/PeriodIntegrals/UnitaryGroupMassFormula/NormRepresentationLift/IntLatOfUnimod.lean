module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.NormRepLift

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NormRepLift

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

def NormRepStep : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ t : TermsOf D u' F0 Λ,
      IsRel Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F t → IsGen Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D) t →
        ∃ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E),
          Formalism.L2.SG.TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F' ∧ AdmWit Λ (gS D) (lf D F0) F' 1

end PI.NormRepLift
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.FrameActOneAdd

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem Xflag_mono (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢
    omega)

theorem X_le_orth (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro x hx
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  refine span_zero (φ := S.hT y) (fun z hz => ?_) hx
  obtain ⟨i, rfl⟩ := hz
  rw [herm_eq, span_zero (φ := S.hT (F.fl.e i)) (fun z hz => by
    obtain ⟨k, rfl⟩ := hz
    exact F.fl.e_iso i k) hy, star_zero]

theorem NLam_mul (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) {n₁ n₂ : S.V ≃ₗ[E] S.V}
    (h₁ : n₁ ∈ NLam Λ F) (h₂ : n₂ ∈ NLam Λ F) : n₁ * n₂ ∈ NLam Λ F := by
  apply PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul <;> assumption

theorem modG_of_mem (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x : S.V}
    (hx : x ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ModG S Λ g x := by
  intro P hP
  haveI := P.isPrime
  show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem modG_add (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x y : S.V} (hx : ModG S Λ g x) (hy : ModG S Λ g y) :
    ModG S Λ g (x + y) := by
  intro P hP
  exact Submodule.add_mem _ (hx P hP) (hy P hP)

theorem modG_map (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (n : S.V ≃ₗ[E] S.V) (hn : Formalism.HermitianLatticesTheory.gmap n Λ = Λ)
    {x : S.V} (hx : ModG S Λ g x) : ModG S Λ g (n x) := by
  intro P hP
  have hx' := hx P hP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := hx'
  show ∃ s ∈ P.asIdeal.primeCompl, s • n x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  refine ⟨s, hs, ?_⟩
  have hmap : (Ideal.span {(g : 𝓞 E)} • Λ).map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) =
      Ideal.span {(g : 𝓞 E)} • Λ := by
    rw [Submodule.map_smul'']
    unfold Formalism.HermitianLatticesTheory.gmap at hn
    rw [hn]
  have hmem := Submodule.mem_map_of_mem (f := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) hsx
  rw [hmap] at hmem
  have he : ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) (s • x) = s • n x :=
    map_smul ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) s x
  rw [he] at hmem
  exact hmem

theorem frameAct_mem (Λ : Submodule (𝓞 E) S.V) {n : ℕ} (f : Fin n → S.V) (hf : ∀ c, f c ∈ Λ)
    (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) : frameAct f Q b ∈ Λ := by
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [smul_coe]
  exact Λ.smul_mem _ (hf a)

theorem frameAct_one_add {n : ℕ} (f : Fin n → S.V) (g : 𝓞 E) (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    frameAct f (1 + g • Q) b = f b + g • frameAct f Q b := by
  have h1 := frameAct_one f b
  unfold frameAct at h1 ⊢
  simp only [smul_coe] at h1 ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, h1,
    mul_smul, Finset.smul_sum]

theorem exists_undo (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (F : LFlag S r T) (g : 𝓞 E)
    (hrow : ∀ (a : Fin r) (t : Fin (r + 1) → 𝓞 E), ∃ v ∈ Λ, ∃ l : 𝓞 E,
      (l : E) + star (l : E) = -S.hT v v ∧ (∀ i, i ≤ a → S.hT v (F.fl.e i) = 0) ∧
      ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 E, S.hT v (frame F c) = ((t c + g * q : 𝓞 E) : E))
    (hfe : ∀ a, F.fl.e a ∈ Λ)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : UniUp ξ) :
    ∃ n ∈ NLam Λ F, ∃ M, ActsBy n (frame F) M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  have hone : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    refine ⟨⟨Subgroup.one_mem _, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
    · rw [gmap_eq_iff]
      exact ⟨fun y hy => hy, fun y hy => ⟨y, hy, rfl⟩⟩
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
  have hrow' : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → 𝓞 E, ∃ w : Fin (r + 1) → 𝓞 E,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧
      (∃ n ∈ NLam Λ F, ActsBy n (frame F) (1 + rowMat a w)) := by
    intro a ha t
    obtain ⟨v, hv, l, hl, hperp, hcong⟩ := hrow ⟨a.val, ha⟩ t
    have hca : Fin.castSucc (⟨a.val, ha⟩ : Fin r) = a := Fin.ext rfl
    rw [hca] at hcong
    choose q hq using hcong
    let w : Fin (r + 1) → 𝓞 E := fun c => if h : a < c then t c + g * q c h else 0
    have hee : S.hT (F.fl.e ⟨a.val, ha⟩) (F.fl.e ⟨a.val, ha⟩) = 0 := F.fl.e_iso _ _
    have hve : S.hT v (F.fl.e ⟨a.val, ha⟩) = 0 := hperp _ le_rfl
    have hev : S.hT (F.fl.e ⟨a.val, ha⟩) v = 0 := by rw [herm_eq, hve, star_zero]
    have hw : ∀ c, S.hT v (frame F c) = (w c : E) := by
      intro c
      by_cases hc : a < c
      · simp only [w, dif_pos hc]
        exact hq c hc
      · simp only [w, dif_neg hc]
        have hcr : c.val < r := by
          have h' : ¬ a.val < c.val := fun h => hc (Fin.lt_def.mpr h)
          omega
        obtain ⟨c', rfl⟩ : ∃ c' : Fin r, Fin.castSucc c' = c := ⟨⟨c.val, hcr⟩, Fin.ext rfl⟩
        have hfc : frame F (Fin.castSucc c') = F.fl.e c' := by
          show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc c') = F.fl.e c'
          exact Fin.snoc_castSucc ..
        have hle : c' ≤ (⟨a.val, ha⟩ : Fin r) := by
          have h' : ¬ a.val < c'.val := fun h => hc (Fin.lt_def.mpr (by simpa using h))
          exact Fin.le_def.mpr (by simp only; omega)
        rw [hfc, hperp c' hle]
        simp
    refine ⟨w, fun c hc => ?_, fun c hc => ⟨q c hc, by simp only [w, dif_pos hc]⟩, ?_⟩
    · have hnc : ¬ a < c := not_lt.mpr hc
      simp only [w, dif_neg hnc]
    · refine ⟨tvEquiv (F.fl.e ⟨a.val, ha⟩) v (l : E) hee hev hve,
        tv_mem_NLam Λ hint F ⟨a.val, ha⟩ (hfe _) v hv hperp l hl hee hev hve, ?_⟩
      have hact := tv_actsBy F ⟨a.val, ha⟩ v (l : E) hee hev hve w hw
      rw [hca] at hact
      exact hact
  obtain ⟨M, ⟨n, hn, hact⟩, Q, hQ⟩ := row_elim g (fun M => ∃ n ∈ NLam Λ F, ActsBy n (frame F) M)
    ⟨1, hone, actsBy_one _⟩
    (fun M N hM hN => by
      obtain ⟨n₁, h₁, a₁⟩ := hM
      obtain ⟨n₂, h₂, a₂⟩ := hN
      exact ⟨n₁ * n₂, NLam_mul Λ F h₁ h₂, actsBy_mul a₁ a₂⟩)
    hrow' ξ hξ
  exact ⟨n, hn, M, hact, Q, hQ⟩

end PI.NRL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.IntLatOfUnimod

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowVec (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  PrimeHyp D u T' →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ (a : Fin D.R.rS) (t : Fin (D.R.rS + 1) → 𝓞 D.host.E),
      ∃ v ∈ Λ, ∃ l : 𝓞 D.host.E, (l : D.host.E) + star (l : D.host.E) = -(VS D).hT v v ∧
        (∀ i, i ≤ a → (VS D).hT v (F0.e i) = 0) ∧
        ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 D.host.E,
          (VS D).hT v (frame (lf D F0) c) = ((t c + (gS D : 𝓞 D.host.E) * q : 𝓞 D.host.E) : D.host.E)

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

def mapFlag (n : S.V ≃ₗ[E] S.V) (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (F : FlagG S r T) :
    FlagG S r T where
  e := fun a => n (F.e a)
  z := n F.z
  e_indep := F.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker
  e_iso := fun a b => by rw [hn]; exact F.e_iso a b
  z_orth := fun a => by rw [hn]; exact F.z_orth a
  z_norm := by rw [hn]; exact F.z_norm

theorem frame_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (F : LFlag S r T)
    (zt : S.V) (b : Fin (r + 1)) :
    frame (⟨mapFlag n hn F.fl, zt⟩ : LFlag S r T) b = n (frame F b) := by
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem intLat_of_unimod (Λ : Submodule (𝓞 E) S.V) (h : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) : IntLat Λ := by
  intro x hx y hy
  rw [← h] at hy
  have hy' : y ∈ Formalism.E.hdual S.hT Λ := hy
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hy'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hy' x hx)
  exact ⟨o, ho.symm⟩

theorem normRepStep_of (D : D7) (u u' : D.what₂.Word) (hS : TermStable D u u')
    (hP : PrimeHyp D u (Tu D u')) (hV : RowVec D u (Tu D u')) : PI.NormRepLift.NormRepStep D u u' := by
  intro F0 Λ hΛ t _ _
  obtain ⟨⟨F1, hF1⟩, rfl⟩ := Quot.exists_rep t
  obtain ⟨ξ, hAdm⟩ := hF1.2.1
  have hint : IntLat Λ := intLat_of_unimod Λ hΛ.2.1.2.1
  have hfe : ∀ a, (lf D F0).fl.e a ∈ Λ := fun a => e_mem_lam D F0 Λ hΛ a
  have hfr : ∀ c, frame (lf D F0) c ∈ Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => simpa [frame, FlagG.fvec] using hΛ.2.1.2.2.1.1
    | cast i => simpa [frame, FlagG.fvec] using hfe i
  obtain ⟨n, hn, M, hM, Q, hQ⟩ := exists_undo Λ hint (lf D F0) (gS D : 𝓞 D.host.E)
    (hV hP F0 Λ hΛ) hfe ξ ⟨hAdm.1, hAdm.2.1⟩
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn.1.1
  let F2 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) := ⟨mapFlag n hiso F1.fl, n F1.zt⟩
  have hDC : DCRel Λ (lf D F0) F1 F2 :=
    ⟨n, hn, 1, one_mem_NLam Λ F1, fun a => by
      induction a using Fin.lastCases with
      | last => simp [F2, frame, FlagG.fvec, mapFlag]
      | cast i => simp [F2, frame, FlagG.fvec, mapFlag], by simp [F2]⟩
  have hP2 : PD D Λ (lf D F0) u' F2 := hS F0 Λ hΛ ⟨F1, hF1⟩ F2 hDC
  have hq : Formalism.L2.SG.TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F2, hP2⟩ =
      Quot.mk (Formalism.L2.SG.TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u')) ⟨F1, hF1⟩ :=
    (Quot.sound (r := Formalism.L2.SG.TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u'))
      (a := ⟨F1, hF1⟩) (b := ⟨F2, hP2⟩) hDC).symm
  refine ⟨F2, ⟨hP2, hq⟩, ?_, ?_, ?_⟩
  · intro a b hab; exact Matrix.one_apply_ne (ne_of_lt hab).symm
  · intro a; exact Matrix.one_apply_eq a
  · intro b
    rw [frameAct_one]
    change ModG (VS D) Λ (gS D) (frame ⟨mapFlag n hiso F1.fl, n F1.zt⟩ b - frame (lf D F0) b)
    rw [frame_mapFlag n hiso F1]
    have e1 : n (frame F1 b) - frame (lf D F0) b =
        n (frame F1 b - frameAct (frame (lf D F0)) ξ b) +
          (frameAct (frame (lf D F0)) (M * ξ) b - frame (lf D F0) b) := by
      rw [map_sub, actsBy_frameAct hM]; abel
    rw [e1]
    refine modG_add Λ _ (modG_map Λ _ n hn.1.2 (hAdm.2.2 b)) (modG_of_mem Λ _ ?_)
    rw [hQ, frameAct_one_add, add_sub_cancel_left]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (frameAct_mem Λ _ hfr Q b)

end PI.NRL
end
end
end
