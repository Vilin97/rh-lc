module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestHLTransport
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsRingChange
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
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RingIndep

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem lpRingIndep_of (h1 : RestRSIso) (h2 : RestHLTransport) : LPRingIndep := by
  unfold LPRingIndep
  intro p n' R₁ R₂ m r lam0 t D κ cStar hLP
  obtain ⟨I⟩ := h1 p n' R₁ R₂
  obtain ⟨Φ, Ψ, hΨ, hLat, hEdge, hHL, hHLe, hdim⟩ := h2 p n' R₁ R₂ I m lam0

  have hwK : ∀ z : ℤ, I.φK (algebraMap R₁.O R₁.Kf R₁.w ^ z) = algebraMap R₂.O R₂.Kf R₂.w ^ z := by
    intro z; rw [map_zpow₀, I.hOK, I.hw]
  have hpK : ∀ z : ℤ, I.φK ((p : R₁.Kf) ^ z) = (p : R₂.Kf) ^ z := by
    intro z; rw [map_zpow₀, map_natCast]

  let back : Edge R₂.W R₂.Qq (m + 1) → Edge R₁.W R₁.Qq (m + 1) := fun e => ⟨Φ.symm e.src, Φ.symm e.tgt⟩
  have hback : ∀ e, (⟨Φ (back e).src, Φ (back e).tgt⟩ : Edge R₂.W R₂.Qq (m + 1)) = e := by
    intro e; cases e; simp [back]
  have hbackEdge : ∀ e, IsEdge p n' r e → IsEdge p n' r (back e) := by
    intro e he; rw [hEdge r (back e), hback]; exact he
  have hHLe' : ∀ e x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 (back e) ↔ Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 e := by
    intro e x; have h := hHLe (back e) x; rwa [hback] at h
  unfold LPprime at hLP ⊢
  obtain ⟨hc, hall⟩ := hLP
  refine ⟨hc, fun L hL => ?_⟩
  have hL1 : IsLattice R₁.W (Φ.symm L) := by rw [hLat, Φ.apply_symm_apply]; exact hL
  have hAt := hall _ hL1
  unfold LPprimeAt at hAt ⊢
  obtain ⟨M, e, F, he, hF, hF', n, hn, hG⟩ := hAt
  refine ⟨M, fun i => ⟨Φ (e i).src, Φ (e i).tgt⟩, fun i => Ψ (F i), ?_, ?_, ?_, n, ?_, ?_⟩
  · intro i
    refine ⟨(hEdge r (e i)).1 (he i).1, ?_⟩
    show Φ (e i).tgt = L
    rw [(he i).2, Φ.apply_symm_apply]
  · intro i
    have hFi := hF i
    simp only [Nsrc, Re, Submodule.mem_inf, Submodule.mem_iInf] at hFi ⊢
    refine ⟨?_, ?_⟩
    · have h := sl_scale I.φK Ψ hΨ _ (hHL (e i).src) hFi.1
      rwa [hwK] at h
    · intro e' he'
      have hb : IsEdge p n' r (back e') ∧ (back e').src = (e i).src := by
        refine ⟨hbackEdge e' he'.1, ?_⟩
        show Φ.symm e'.src = (e i).src
        rw [he'.2]; exact Φ.symm_apply_apply _
      have h := sl_scale I.φK Ψ hΨ _ (hHLe' e') (hFi.2 (back e') hb)
      rwa [hwK] at h
  · intro i e' he' hsrc hne
    have hb : (back e').src = (e i).src := by
      show Φ.symm e'.src = (e i).src
      rw [hsrc]; exact Φ.symm_apply_apply _
    have hne' : back e' ≠ e i := by
      intro h; apply hne; rw [← hback e', h]
    have hx := hF' i (back e') (hbackEdge e' he') hb hne'
    simp only [Re] at hx ⊢
    have h := sl_scale2 I.φK Ψ hΨ _ _ (hHLe' e') hx
    rwa [hwK, hwK] at h
  · rw [← hdim]; exact hn
  ·
    have hN : ∀ G, G ∈ Ntgt p n' R₁.ι R₁.σ R₁.w r lam0 t (Φ.symm L) →
        dT I.φK Ψ hΨ G ∈ Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L := by
      intro G hG
      simp only [Ntgt, Re', Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢
      refine ⟨?_, ?_⟩
      · have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHL (Φ.symm L)) hG.1
        rwa [hwK, Φ.apply_symm_apply] at h
      · intro e' he'
        have hb : IsEdge p n' r (back e') ∧ (back e').tgt = Φ.symm L := by
          refine ⟨hbackEdge e' he'.1, ?_⟩
          show Φ.symm e'.tgt = Φ.symm L
          rw [he'.2]
        have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHLe' e') (hG.2 (back e') hb)
        rwa [hwK] at h
    unfold GoodRankK at hG ⊢
    obtain ⟨u, Mt, hu⟩ := hG
    have hdTv : ∀ (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) v, dT I.φK Ψ hΨ G v = I.φK (G (Ψ.symm v)) :=
      fun _ _ => rfl
    let u₂ : (Fin n → R₂.O) →ₗ[R₂.O] Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L :=
      { toFun := fun x => ⟨dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)), hN _ (u _).2⟩
        map_add' := by
          intro x y
          have hx : (fun j => I.φO.symm ((x + y) j)) =
              (fun j => I.φO.symm (x j)) + (fun j => I.φO.symm (y j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          simp only [hx, map_add (f := _), Submodule.coe_add, LinearMap.add_apply, hdTv]
        map_smul' := by
          intro c x
          have hx : (fun j => I.φO.symm ((c • x) j)) = I.φO.symm c • (fun j => I.φO.symm (x j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show I.φK ((u fun j => I.φO.symm ((c • x) j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) (Ψ.symm v)) =
            (c • (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)) : Module.Dual R₂.Kf (Vsp R₂.Kf lam0))) v
          rw [hx, map_smul, LinearMap.smul_apply, hdTv]
          simp only [SetLike.val_smul, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, I.hOK, RingEquiv.apply_symm_apply] }
    refine ⟨u₂, Mt.map I.φO, ?_⟩
    intro x j
    have hbe : ∀ i (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)),
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ G) = I.φK (be p r lam0 (F i) G) := by
      intro i G
      simp only [be]
      rw [← hpK, ← hΨ, dT_apply]
    have hx := hu (fun j => I.φO.symm (x j)) j
    show ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j))) =
      algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j)
    calc ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
          be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)))
        = ∑ i, I.φK (algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hbe, map_mul, I.hOK]
      _ = I.φK (∑ i, algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) :=
          (map_sum _ _ _).symm
      _ = I.φK (algebraMap R₁.O R₁.Kf ((p : R₁.O) ^ D * I.φO.symm (x j))) := by rw [hx]
      _ = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j) := by
          rw [I.hOK, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HLepolyTr

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section

variable {p n' : ℕ} {R₁ R₂ : RS p n'} (I : RSIso R₁ R₂) {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem pm_symm (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) :
    I.symm.JO.pm (I.JO.pm P) = P := by
  show MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) (MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) P) = P
  have h : (I.φK.symm : R₂.Kf →+* R₁.Kf).comp (I.φK : R₁.Kf →+* R₂.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

theorem pm_symm' (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₂.Kf) :
    I.JO.pm (I.symm.JO.pm P) = P := by
  show MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) (MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) P) = P
  have h : (I.φK : R₁.Kf →+* R₂.Kf).comp (I.φK.symm : R₂.Kf →+* R₁.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

def PsiV : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0 where
  toFun x := ⟨I.JO.pm x.1, Vsp_tr I lam0 x.1 x.2⟩
  invFun y := ⟨I.symm.JO.pm y.1, Vsp_tr I.symm lam0 y.1 y.2⟩
  left_inv x := Subtype.ext (pm_symm I x.1)
  right_inv y := Subtype.ext (pm_symm' I y.1)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem HLpoly_tr (L : Submodule R₁.W (Fin (m + 1) → R₁.Qq))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => extO R₁.O R₁.ι R₁.σ s.val L)) :
    I.JO.pm P ∈ Hten R₂.O lam0 (fun s => extO R₂.O R₂.ι R₂.σ s.val (mapSub I.JW L)) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => extO R₁.O R₁.ι R₁.σ s.val L) (P := P) hP
  simp only [extO_tr] at h
  exact h

theorem HLepoly_tr (e : Edge R₁.W R₁.Qq (m + 1))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e)) :
    I.JO.pm P ∈ Hten R₂.O lam0
      (fun s => LeAt p R₂.ι R₂.σ R₂.w s.val ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e) (P := P) hP
  simp only [LeAt_tr] at h
  exact h

end

theorem restHLTransport : RestHLTransport := by
  intro p n' R₁ R₂ I m lam0
  have hΨ : ∀ (c : R₁.Kf) (v : Vsp R₁.Kf lam0), PsiV I lam0 (c • v) = I.φK c • PsiV I lam0 v := by
    intro c v
    exact Subtype.ext (map_smul' _ c v.1)
  refine ⟨mapSubEquiv I.JW, PsiV I lam0, hΨ, fun L => isLattice_mapSub_iff I.JW L, fun r e => ?_, fun L x => ?_,
    fun e x => ?_, ?_⟩
  · constructor
    · exact isEdge_mapSub I.JW p n' r
    · intro h
      have h2 := isEdge_mapSub I.JW.symm p n' r h
      simp only at h2
      have h3 : mapSub I.JW.symm (mapSub I.JW e.src) = e.src := mapSub_symm _ _
      have h4 : mapSub I.JW.symm (mapSub I.JW e.tgt) = e.tgt := mapSub_symm _ _
      have h5 : (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) = e := by rw [h3, h4]
      have h6 : IsEdge p n' r (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) := h2
      rwa [h5] at h6
  · constructor
    · intro hx
      exact HLpoly_tr I lam0 L x.1 hx
    · intro hx
      have h2 := HLpoly_tr I.symm lam0 (mapSub I.JW L) (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW L) = L := mapSub_symm I.JW L
      rw [h3] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · constructor
    · intro hx
      exact HLepoly_tr I lam0 e x.1 hx
    · intro hx
      have h2 := HLepoly_tr I.symm lam0 ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩ (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW e.src) = e.src := mapSub_symm I.JW _
      have h3' : mapSub I.symm.JW (mapSub I.JW e.tgt) = e.tgt := mapSub_symm I.JW _
      simp only [h3, h3'] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · unfold dimV Module.finrank
    rw [rank_eq_of_equiv_equiv I.φK (PsiV I lam0) I.φK.bijective hΨ]

theorem lpRingIndep_of' (h : RestRSIso) : LPRingIndep := lpRingIndep_of h restHLTransport

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestOIso : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (φW : R₁.W ≃+* R₂.W),
    ∃ φO : R₁.O ≃+* R₂.O, (∀ x, φO (R₁.jO x) = R₂.jO (φW x)) ∧ φO R₁.w = R₂.w

theorem restRSIso_of (hW : WittIdent) (hO : RestOIso) : RestRSIso := by
  intro p n' R₁ R₂
  have s₁ := R₁.std.1
  have s₂ := R₂.std.1
  haveI : Fact (Nat.Prime p) := ⟨s₁.prime⟩
  haveI := s₁.frac_alt
  haveI := s₂.frac_alt
  haveI := s₁.frac_O
  haveI := s₂.frac_O
  obtain ⟨φ₁, h₁⟩ := hW p n' R₁.W R₁.Qq R₁.O R₁.Kf R₁.ι R₁.σ R₁.jO R₁.w s₁
  obtain ⟨φ₂, h₂⟩ := hW p n' R₂.W R₂.Qq R₂.O R₂.Kf R₂.ι R₂.σ R₂.jO R₂.w s₂
  obtain ⟨φO, hj, hw⟩ := hO p n' R₁ R₂ (φ₁.symm.trans φ₂)
  let φQ : R₁.Qq ≃+* R₂.Qq := IsFractionRing.ringEquivOfRingEquiv (φ₁.symm.trans φ₂)
  let φK : R₁.Kf ≃+* R₂.Kf := IsFractionRing.ringEquivOfRingEquiv φO
  have hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq ((φ₁.symm.trans φ₂) x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x) := by
    have key : (φQ : R₁.Qq →+* R₂.Qq).comp (R₁.σ : R₁.Qq →+* R₁.Qq) =
        (R₂.σ : R₂.Qq →+* R₂.Qq).comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      obtain ⟨v, rfl⟩ := φ₁.surjective u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [h₁ v, hWQ, hWQ]
      simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
      rw [h₂ v]
    exact fun x => RingHom.congr_fun key x
  have hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x) := by
    have key : (φK : R₁.Kf →+* R₂.Kf).comp R₁.ι = R₂.ι.comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [s₁.ι_comp, hOK, hj, hWQ, s₂.ι_comp]
    exact fun x => RingHom.congr_fun key x
  exact ⟨⟨φ₁.symm.trans φ₂, φQ, φO, φK, hWQ, hOK, hι, hσ, hj, hw⟩⟩

theorem lpRingIndep_of'' (hW : WittIdent) (hO : RestOIso) : LPRingIndep := lpRingIndep_of' (restRSIso_of hW hO)

end Formalism.MainNotions.flipOneThree.Pf

end
end
end
