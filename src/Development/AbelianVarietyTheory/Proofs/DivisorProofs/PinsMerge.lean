module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDDdBCIff
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots

section

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

theorem exists_coeff_roots (c : Coeff l) {z w : ℂ} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (hw : ∃ m : ℕ, 0 < m ∧ w ^ m = 1) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ z ∈ c'.F ∧ w ∈ c'.F := by
  have hi : ∀ x : ℂ, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → IsIntegral ℚ x := by
    rintro x ⟨m, hm, h⟩
    exact IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := c.fin
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({z, w} : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl)
      · exact hi _ hz
      · exact hi _ hw)
  have hle : c.F ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_left
  have hle' : IntermediateField.adjoin ℚ ({z, w} : Set ℂ) ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_right
  exact ⟨⟨c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ), inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, hle' (IntermediateField.subset_adjoin _ _ (by simp)),
    hle' (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem exists_coef_ext {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ : K →+* ℂ} (σ' : K' →+* ℂ)
    (hσ : ∀ a, σ' (j a) = σ a) {I : Type} [Fintype I] (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) : ∃ c₁ : VV K' lam →ₛₗ[σ'] W, ∀ (v : VV K lam) (v' : VV K' lam),
      (v' : Pol K' I n) = MvPolynomial.map j (v : Pol K I n) → c₁ v' = c₀ v := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.exists_extend (p := VV K lam) (LinearMap.id : VV K lam →ₗ[K] VV K lam)
  have hp' : ∀ v : VV K lam, p v = v := fun v => LinearMap.congr_fun hp v
  let C : Pol K' I n →ₛₗ[σ'] W :=
    { toFun := fun F => Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr F)
        fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))
      map_add' := fun F F' => by
        rw [map_add (f := _)]
        exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
      map_smul' := fun a F => by
        rw [map_smul, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
        simp [mul_smul] }
  have hC : ∀ m a, C (MvPolynomial.monomial m a) = σ' a • c₀ (p (MvPolynomial.monomial m 1)) := fun m a => by
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials _ K' m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smulₛₗ]
    congr 1
    show Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr (MvPolynomial.basisMonomials _ K' m))
      (fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))) = _
    rw [Module.Basis.repr_self, Finsupp.sum_single_index (by simp), map_one, one_smul]
  have key : ∀ F : Pol K I n, C (MvPolynomial.map j F) = c₀ (p F) := by
    intro F
    induction F using MvPolynomial.induction_on' with
    | monomial m a =>
      rw [MvPolynomial.map_monomial, hC, hσ, ← map_smulₛₗ, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    | add F F' h h' => rw [map_add (f := _), map_add (f := _), h, h', map_add (f := _), map_add (f := _)]
  exact ⟨C.comp (VV K' lam).subtype, fun v v' h => by
    show C v' = _
    rw [h, key, hp']⟩

theorem covPin_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u ≠ 0)
    (h : d.IsLev ∧ d.l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) :
    (covBC hle d u).IsLev ∧ (covBC hle d u).l₂.A = 1 ∧
      ∃ _ : StarRing (𝓞 E), IsNab (covBC hle d u).Xo₂ (covBC hle d u).c₂ (covBC hle d u).nab₂ := by
  obtain ⟨h1, h2, s, h3⟩ := h
  exact ⟨GlobalTheory.LevelCoverDatum.isLev_smul (ddBC hle d) (GlobalTheory.FieldBCModel.isLev_ddBC hle d h1) u hu, h2, s,
    GlobalTheory.FieldBCModel.isNab_nabBC (le_covCoeff hle d) d.nab₂ h3⟩

theorem phiHat_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) (φ : (Fin n → LevQc Dw d.l₂) → c.F)
    (w : c.F) (q : Fin n → LevQ Dw d.l₂) (h : d.eF w = phiHat d.c₂ (fun x => d.eF (φ x)) q) :
    (covBC hle d u).eF (incF c c' hle w) =
      phiHat (covBC hle d u).c₂ (fun x => (covBC hle d u).eF (incF c c' hle (φ x))) q := by
  have e := congrArg (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)) h
  refine Eq.trans (Subtype.ext rfl) (e.trans ?_)
  unfold phiHat
  have hz : zetaM (covCoeff hle d) = incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (zetaM d.c₂) := by
    unfold zetaM; rw [map_pow]; rfl
  refine (AddMonoidHom.map_finsum_of_injective
    (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)).toAddMonoidHom (RingHom.injective _) _).trans ?_
  refine finsum_congr fun x => ?_
  show incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (_ * _) = _
  rw [map_mul, map_zpow₀, ← hz]
  rfl

theorem epIs_map (hle : c.F ≤ c'.F) {bad : ℕ} {B : Ideal (𝓞 E) → c.F} {epF : Submodule (𝓞 E) (Fin n → E) → c.F}
    (h : EpIs (Dw := Dw) c bad B epF) :
    EpIs (Dw := Dw) c' bad (fun I => incF c c' hle (B I)) (fun L => incF c c' hle (epF L)) := by
  intro L cc h1 h2 h3 h4 h5
  obtain ⟨q, a, b, e⟩ := h L cc h1 h2 h3 h4 h5
  exact ⟨q, a, b, by simp only [e, map_mul, map_inv₀, map_ratCast]⟩

theorem isThClsD_covBC_one (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u = 1) {Cl : Type} [Fintype Cl]
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    {Vs' : Type} [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (x : Cl → Vs) (x' : Cl → Vs') (hx : ∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k)))
    (hd : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) :
    IsThClsD Xo c' (covBC hle d u) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol)
      (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) := by
  subst hu
  have h' := (GlobalTheory.ClassSumFieldChange.isThClsD_ddBC_iff E H Dw l Xo c c' hle n d Cl w La Nc gam vol ep Vs io Vs' io' x x'
    hx hd a m f hf).2 h
  intro k _ _ _ i hk y y₂ hy
  obtain ⟨vc, h1, h2⟩ := @h' k _ _ _ i hk y y₂ hy
  refine ⟨vc, h1, h2.trans ?_⟩
  have e : (covBC hle d 1).cδ = (ddBC hle d).cδ := one_smul (covCoeff hle d).F (rulBC (le_covCoeff hle d) d.cδ)
  rw [e]
  rfl

theorem isBC_rulBC_trans {c₀ : Coeff l} (h₀ : c₀.F ≤ c.F) (hle : c.F ≤ c'.F) (h₁ : c₀.F ≤ c'.F)
    {a : (E →+* ℂ) × ℕ → ℕ} {k m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a k) {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀}
    (h : IsBC h₀ f as fs) : IsBC h₁ (rulBC hle f) (fun i => incF c c' hle (as i)) fs := by
  intro S _ _ _ hS y
  letI := resAlg hle S
  rw [GlobalTheory.FieldBCModel.evR_rulBC hle hf.1 (fun _ => rfl) y, h S (fun a => hS a) _]
  rfl

end Gen

section Forms

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ} (t : T0) {Cl : Type} (h : Cl → GA D (Vc D i))
  (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

theorem adForms_ext {Gp Γ W I : Type} [Group Gp] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gp}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gp} {χ : J →* ℂˣ} {F F' : Gp → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (hF' : F' ∈ Bridge.AdForms ι ρ J χ) (hJ : J' ≤ J) {y : I → Gp} (hr : Bridge.IsReps ι J' y)
    (h : ∀ k, F (y k) = F' (y k)) : F = F' := by
  funext g
  obtain ⟨k, ⟨γ, κ, rfl⟩, -⟩ := hr g
  have h1 := hF γ (y k) ⟨κ, hJ κ.2⟩
  have h2 := hF' γ (y k) ⟨κ, hJ κ.2⟩
  rw [h k] at h1
  exact h1.trans h2.symm

theorem place_unique (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) {y y' : (R.HV i t).H} {x : Cl → VsV D i K'}
    (hy : Place R i t h c0' y x) (hy' : Place R i t h c0' y' x) : y = y' := by
  exact (hV i t).1 (adForms_ext ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y))
    ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y')) hJ hr fun k => (hy k).trans (hy' k).symm)


open Classical in
def thAdOf (v₀ : (R.MW i (sg0 D A)).Vec) (x : Cl → VsV D i K') : AutQ (Wc D i) → ℂ :=
  if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0

theorem thAdIs_thAdOf (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (v₀ : (R.MW i (sg0 D A)).Vec) :
    ThAdIs R i t h c0' v₀ (thAdOf R i t h c0' v₀) := by
  intro y x hy
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  have e := place_unique R i t h c0' hV hJ hr hx.choose_spec hy
  exact (dif_pos hx).trans (congrArg (fun y => onQ (Wc D i) (R.thF i t y v₀)) e)

end Forms

end GlobalTheory.OneMapAll
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge

section

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩


end Merge

end GlobalTheory.OneMapAll
end
end
end
