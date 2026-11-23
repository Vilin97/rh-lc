module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0ZeroOfFixed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PhiTransport
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusExpEqOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.PerSpan GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

theorem lie_equiv {S : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over (Sp ℂ)} [GrpObj G'] {z : Sp ℂ ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G z φ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (MV : LieModel G' (𝟙 (Sp ℂ)) V) (Mz : LieModel G z V') :
    ∃ Φ : V ≃ₗ[ℂ] V', ∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (epsAt (𝟙 (Sp ℂ))).hom (epsAt z).hom (by simp)
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (𝟙 (Sp ℂ)) z (Category.id_comp _).symm
  have h1 : (1 : Over.mk z ⟶ G).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G').left ≫ φ := by
    rw [← hρ₀, map_one]
  have tan : ∀ v : epsAt (𝟙 (Sp ℂ)) ⟶ G', IsTanAt G z (ρ v) ↔ IsTanAt G' (𝟙 _) v := by
    intro v
    unfold IsTanAt
    constructor
    · intro h
      refine hp.1.hom_ext ?_ ?_
      · rw [← h1, ← h, Category.assoc]
        exact congrArg _ (hρ v).symm
      · rw [Category.assoc, Over.w v, Over.w (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G')]
        exact TorusModel.fst_eps (𝟙 (Sp ℂ))
    · intro h
      rw [h1, ← h, Category.assoc]
      exact congrArg _ (hρ v)
  choose f hf using fun x => Mz.onto _ ((tan _).2 (MV.tan x))
  have hl : ∀ x, (Mz.pt (f x)).left = (MV.pt x).left ≫ φ := fun x => by
    rw [hf]
    exact hρ _
  let F : V →ₗ[ℂ] V' :=
    { toFun := f
      map_add' := fun x y => Mz.inj (by
        rw [Mz.add, hf, hf, hf, MV.add]
        exact map_mul ρ _ _)
      map_smul' := fun c x => Mz.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, Mz.smul, hl, hl, MV.smul, Category.assoc])) }
  refine ⟨LinearEquiv.ofBijective F ⟨fun x y h => ?_, fun y => ?_⟩, hl⟩
  · have h' : f x = f y := h
    refine MV.inj (ρ.injective ?_)
    exact (hf x).symm.trans ((congrArg Mz.pt h').trans (hf y))
  · obtain ⟨x, hx⟩ := MV.onto (ρ.symm (Mz.pt y)) ((tan _).1 (by rw [ρ.apply_symm_apply]; exact Mz.tan y))
    refine ⟨x, Mz.inj ?_⟩
    show Mz.pt (f x) = _
    rw [hf, hx]
    exact ρ.apply_symm_apply _

theorem torus_deriv {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)
    (MT : LieModel (splitTorus (Sp ℂ) X) (𝟙 _) (X →+ ℂ)) (hMT : IsCocharLie MT) (δ : X →+ ℂ) :
    IsDerivAt0 (fun w => (torusExp β w).left) (fun a => δ (β a)) (MT.pt δ).left := by
  obtain ⟨v, H⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_torusExp β) (fun a => δ (β a))
  have hv := GlobalTheory.VerticalDeriv.isDerivAt0_vertical (splitTorus (Sp ℂ) X).hom (𝟙 (Sp ℂ))
    (e := fun w => (torusExp β w).left) (fun w => Over.w (torusExp β w)) H
  let v' : epsAt (𝟙 (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X := Over.homMk v hv
  have h0 : torusExp β (0 : Fin d → ℂ) = 1 := by
    have := torusExp_add β (0 : Fin d → ℂ) 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ht : IsTanAt (splitTorus (Sp ℂ) X) (𝟙 _) v' := H.1.trans (congrArg (·.left) h0)
  obtain ⟨δ', hδ'⟩ := MT.onto v' ht
  have e : δ' = δ := by
    ext χ
    have H2 := GlobalTheory.FibreDeriv.isDerivAt0_comp H (pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)))
    have h3 := H2.2 ⊤ le_top ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))
    have h4 : (fun z => valAt' ((torusExp β z).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
        ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))) =
        fun z => Complex.exp (pairing β z χ) :=
      funext fun z => (valAt'_torusFst' _ _).trans (torusExp_hol_char β z χ)
    let Lc : (Fin d → ℂ) →L[ℂ] ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) • ContinuousLinearMap.proj a
    have hLc : ∀ w, Lc w = pairing β w χ := fun w => by simp [Lc, pairing]
    have h5 : fderiv ℂ (fun z => Complex.exp (pairing β z χ)) 0 (fun a => δ (β a)) = δ χ := by
      have : HasFDerivAt (fun z => Complex.exp (Lc z)) (Complex.exp (Lc 0) • Lc) 0 := Lc.hasFDerivAt.cexp
      simp only [hLc] at this
      rw [this.fderiv, ContinuousLinearMap.smul_apply, hLc, ← hLc 0, map_zero, Complex.exp_zero, one_smul]

      conv_rhs => rw [← β.sum_repr χ, map_sum]
      simp only [pairing, map_zsmul, zsmul_eq_mul]
    have h6 := hMT δ' χ
    rw [hδ'] at h6
    have h7 : (charVal v' χ).snd = δ' χ := by rw [h6]; simp
    rw [← h7, ← h5, ← h4]
    refine Eq.trans ?_ h3
    congr 1
    unfold charVal
    set g : Sp (DualNumber ℂ) ⟶ Spec (torusRing ZU X) :=
      v'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)) with hg
    have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom = Spec.preimage g := by
      conv_lhs => rw [← Spec.map_preimage g]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have h8 : g.appTop = g.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [← h, h8]
    rfl
  rw [← e, hδ', e]
  exact H

theorem torusExp_eq_one {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X) (w : Fin d → ℂ) :
    torusExp β w = 1 ↔ ∃ δ : X →+ ℤ, w = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ) := by
  have hT : ∀ χ : X, torusHom β w (Multiplicative.ofAdd χ) = expUnit (pairing β w χ) := fun χ => rfl
  have hE : torusExp β w =
      (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))).symm (torusHom β w) := rfl
  constructor
  · intro h1
    have hH : torusHom β w = 1 := by
      have h0 := congrArg (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))) h1
      rw [hE, MulEquiv.apply_symm_apply, map_one] at h0
      exact h0
    have hexp : ∀ a, Complex.exp (w a) = 1 := by
      intro a
      have h2 := congrArg (fun f => f (Multiplicative.ofAdd (β a))) hH
      simp only [hT, MonoidHom.one_apply, pairing_basis] at h2
      have h3 := gamma_expUnit (w a)
      rw [h2, Units.val_one, map_one] at h3
      exact h3.symm
    choose n hn using fun a => Complex.exp_eq_one_iff.1 (hexp a)
    refine ⟨(β.constr ℤ n).toAddMonoidHom, ?_⟩
    funext a
    rw [hn a]
    simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis]
    ring
  · rintro ⟨δ, rfl⟩
    have hH : torusHom β (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = 1 := by
      apply monoidHom_ext_basis β
      intro a
      rw [hT, pairing_basis, MonoidHom.one_apply]
      apply expUnit_eq_one
      show Complex.exp (2 * ↑Real.pi * Complex.I * (δ (β a) : ℂ)) = 1
      rw [mul_comm]
      exact Complex.exp_int_mul_two_pi_mul_I (δ (β a))
    rw [hE, hH, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem torus_lift (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) :
    letI := P.τ.addCommGroup
    ∃ (d : ℕ) (β : Module.Basis (Fin d) ℤ P.τ.X) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ (MT : LieModel (splitTorus (Sp ℂ) P.τ.X) (𝟙 _) (P.τ.X →+ ℂ)), IsCocharLie MT → ∀ δ : P.τ.X →+ ℂ,
        (Mz.pt (h fun a => δ (β a))).left = (MT.pt δ ≫ P.τ.i).left ≫ P.m.φ) ∧
      (∀ z, h z ∈ e.per b ↔ ∃ δ : P.τ.X →+ ℤ, z = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) ∧
      ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
        (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsGrpPullback A P.tB.G (𝟙 _) φ → IsAbLift e b P φ u ℓ →
        ∀ y, ℓ y = 0 ↔ ∃ z, y = h z := by
  letI := P.τ.grpB
  letI := P.τ.addCommGroup
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let β := Module.finBasis ℤ P.τ.X
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  let v : (Fin (Module.finrank ℤ P.τ.X) → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => ρ (torusExp β z ≫ P.τ.i)
  have vadd : ∀ z w, v (z + w) = v z * v w := fun z w => by
    show ρ (torusExp β (z + w) ≫ P.τ.i) = ρ (torusExp β z ≫ P.τ.i) * ρ (torusExp β w ≫ P.τ.i)
    rw [torusExp_add, MonObj.mul_comp]
    exact map_mul ρ _ _
  have vl : (fun z => (v z).left) = fun z => (torusExp β z).left ≫ P.τ.i.left ≫ P.m.φ := funext fun z => by
    rw [← Category.assoc]
    exact hρ _
  have vhol : IsHolTo Set.univ (fun z => (v z).left) := by
    rw [vl]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_torusExp β) _
  obtain ⟨h', -, hh⟩ := exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b)
    (famExpAtPoint e hb) _ Set.univ (fun _ z => v z) isOpen_univ subset_rfl (fun _ _ z w => vadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (v z).left) vhol)
  obtain ⟨hex, -, hder⟩ := hh 0 trivial
  have hex' : ∀ z, e.ex b (h' 0 z) = v z := hex
  have hder' : ∀ z w, IsDerivAt0 (fun z => (v z).left) z w ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h' 0 z) w := hder
  have hmono : Mono P.τ.i := by
    refine ⟨fun a a' haa => P.τ.isKernel.hom_ext haa (toUnit_unique _ _)⟩
  have hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1 := by
    intro z
    have h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η := P.τ.isKernel.w
    have h2 : z ≫ P.τ.i ≫ P.τ.q = 1 := by
      rw [h1, ← Category.assoc, Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    calc (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = (z ≫ P.τ.i ≫ P.τ.q) ≫ P.e.hom := by simp only [Category.assoc]
      _ = 1 := by rw [h2, MonObj.one_comp]
  refine ⟨_, β, h' 0, fun MT hMT δ => ?_, fun z => ?_, fun A _ φ g' u ℓ hA hl y => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (torus_deriv β MT hMT δ) (P.τ.i.left ≫ P.m.φ)
    rw [← vl] at d1
    have d2 := (hder' _ _).1 d1
    rw [Over.comp_left, Category.assoc]
    exact GlobalTheory.VerticalDeriv.isDerivAt0_unique (DiffL.isDerivAt0_pt e hb Mz hL _) d2
  · rw [← torusExp_eq_one]
    show e.ex b (h' 0 z) = 1 ↔ _
    rw [hex']
    refine (map_eq_one_iff ρ ρ.injective).trans ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [← cancel_mono P.τ.i, MonObj.one_comp]
      exact h1
    · show torusExp β z ≫ P.τ.i = 1
      rw [h1, MonObj.one_comp]
  · obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hA (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
    have hl' : ∀ y (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), ρ s = e.ex b y → ρ' (u.ex (ℓ y)) = s ≫ P.τ.q ≫ P.e.hom :=
      fun y s hs => Over.OverMorphism.ext ((hρ' _).trans (hl y s ((hρ s).symm.trans (congrArg (·.left) hs))))
    constructor
    · intro hy
      obtain ⟨Γ₀, hΓ, hd, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R t.G g n M B ψ e b hb
      have hcount : (e.per b).Countable := by
        rw [← hΓ]
        haveI := hd
        have : Countable Γ₀ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      have h0 : (LinearMap.range (h' 0)).mkQ y = 0 := by
        refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hcount.image (LinearMap.range (h' 0)).mkQ) fun c => ?_
        obtain ⟨s, hs⟩ := ρ.surjective (e.ex b (c • y))
        have h1 := hl' _ s hs
        rw [map_smul, hy, smul_zero, (u.ker 0).2 u.Λ.zero_mem] at h1
        have h2 : s ≫ P.τ.q ≫ P.e.hom = 1 := h1.symm.trans (map_one ρ')
        have h3 : s ≫ P.τ.q = 1 := by
          rw [← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]
          exact h2
        let τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X :=
          P.τ.isKernel.lift s (toUnit _) (by rw [h3, Hom.one_def]; rfl)
        have hτ : τ₀ ≫ P.τ.i = s := P.τ.isKernel.lift_fst _ _ _
        obtain ⟨w, hw⟩ := torusExp_surjective β τ₀
        have h4 : e.ex b (h' 0 w) = e.ex b (c • y) := by
          rw [hex', ← hs, ← hτ, ← hw]
        refine ⟨c • y - h' 0 w, ?_, ?_⟩
        · show e.ex b _ = 1
          have := e.add b hb (c • y - h' 0 w) (h' 0 w)
          rw [sub_add_cancel, h4] at this
          exact right_eq_mul.1 this
        · simp only [map_sub, map_smul, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range (h' 0))).2 ⟨w, rfl⟩, sub_zero]
      have : y ∈ LinearMap.range (h' 0) := by simpa using h0
      obtain ⟨z, hz⟩ := this
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      have hcount : (u.Λ : Set (Fin g' → ℂ)).Countable := by
        haveI := u.discrete
        have : Countable u.Λ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      refine GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun c => ?_
      rw [← map_smul, ← map_smul]
      refine (u.ker _).1 (ρ'.injective ?_)
      exact ((hl' _ _ (hex' (c • z)).symm).trans (hQ1 _)).trans (map_one ρ').symm

end LevelTowerAlt.Val
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.CentreIdent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem centre_ident (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (hP : IsPrincipal P.tB) (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρ)
    (hI : P.IsCochars MV I)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ c x, e.ex b (Bb c x) = e.ex b x ≫ t.act.act c)
    (Hb : Matrix (Fin g) (Fin g) ℂ) (hH : Hb.IsHermitian)
    (hW : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, ∃ k : ℤ, (y ⬝ᵥ Hb *ᵥ star y').im = k ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) →
      CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ))
    (I' : Set (Fin g → ℂ)) (hI' : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ∀ y ∈ e.per b, (p ⬝ᵥ Hb *ᵥ star y).im = 0)
    (hrad : ∀ p ∈ I', Hb *ᵥ star p = 0) :
    ∃ Φ : V ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ P.m.φ) ∧
      (∀ a x, Bb a (Φ x) = Φ (ρ a x)) ∧ (∀ x x', hf x x' = Real.pi * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) ∧
      ∀ p, p ∈ I' ↔ ∃ x ∈ I, p = (2 * Real.pi * Complex.I : ℂ) • Φ x := by
  letI := P.τ.addCommGroup
  obtain ⟨Φ, hΦ⟩ := lie_equiv P.m.cart MV Mz
  obtain ⟨d, β, h, t1, t2, t3⟩ := torus_lift e hb P Mz hL
  have key : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
      (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsAbLift e b P φ u ℓ →
      (∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0) ∧ ∀ p q, ℓ p ⬝ᵥ Hm *ᵥ star (ℓ q) = p ⬝ᵥ Hb *ᵥ star q := by
    intro A iA φ g' u Hm χ ℓ hφ hAH hℓ
    obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
    obtain ⟨H', hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
    have hE : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, (y ⬝ᵥ Hb *ᵥ star y').im = (ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im := by
      intro y hy y' hy'
      obtain ⟨k, hk, hc⟩ := hW y hy y' hy'
      rw [hk]
      refine eq_of_forall_exp fun N hN => ?_
      have := GlobalTheory.T.hol_unif_period_matrix_middle E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ y y' hN hy hy'
        (hc N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (k : ℂ) / N))) hN rfl)
      rw [Units.val_mk0] at this
      have c : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
      rw [c]
      exact this
    have k1 : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0 := fun p => by
      rw [hI']
      refine and_congr_right fun hp => ⟨fun h0 => ?_, fun h0 y hy => ?_⟩
      · refine eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_
        obtain ⟨y, hy, rfl⟩ := honto q hq
        rw [← hE p hp y hy, h0 y hy]
      · rw [hE p hp y hy, h0]
        simp
    refine ⟨k1, fun p q => ?_⟩
    rw [← hH2]
    congr 2
    refine herm_unique H' Hb hH1 hH (e.per b) {y | ℓ y = 0} (fun x hx y hy => by rw [hH2, hE x hx y hy]) hH3
      (fun y hy => ?_) (fun p => ?_)
    · obtain ⟨z, rfl⟩ := (t3 A φ g' u ℓ hφ hℓ y).1 hy
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have e1 : z = ∑ a, (z a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
        ext c
        simp [Finset.sum_apply, Pi.single_apply, h2]
      have e2 : ∀ a, Hb *ᵥ star (h (Pi.single a (2 * Real.pi * Complex.I))) = 0 := fun a => by
        refine hrad _ ((k1 _).2 ⟨(t2 _).2 ⟨(β.coord a).toAddMonoidHom, funext fun c => ?_⟩,
          (t3 A φ g' u ℓ hφ hℓ _).2 ⟨_, rfl⟩⟩)
        by_cases hc : c = a
        · subst hc; simp
        · simp [hc, Finsupp.single_apply]

      rw [e1, map_sum, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul, star_smul, Matrix.mulVec_smul, e2, smul_zero]
    · have hp : ℓ p ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)) := by rw [u.full]; trivial
      have : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)), ∃ r ∈ Submodule.span ℝ (e.per b), ℓ r = w := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, hy, rfl⟩ := honto x hx
          exact ⟨y, Submodule.subset_span hy, rfl⟩
        | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
        | add x y _ _ hx hy =>
          obtain ⟨r, hr, rfl⟩ := hx
          obtain ⟨r', hr', rfl⟩ := hy
          exact ⟨r + r', Submodule.add_mem _ hr hr', map_add _ _ _⟩
        | smul c x _ hx =>
          obtain ⟨r, hr, rfl⟩ := hx
          exact ⟨c • r, Submodule.smul_mem _ _ hr, ℓ.map_smul_of_tower c r⟩
      obtain ⟨r, hr, hrp⟩ := this _ hp
      exact ⟨r, hr, by show ℓ (p - r) = 0; rw [map_sub, hrp, sub_self]⟩
  refine ⟨Φ, hΦ, fun a x => ?_, fun x x' => ?_, fun p => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (DiffL.isDerivAt0_pt e hb Mz hL (Φ x)) (t.act.act a).left
    have d2 := PerGram.isDerivAt0_comp_linMap (PerSpan.isHolTo_ex_slice e hb) (Bb a)
      (DiffL.isDerivAt0_pt e hb Mz hL (Bb a (Φ x)))
    have e1 : (fun z => (e.ex b (Bb a z)).left) = fun z => (e.ex b z).left ≫ (t.act.act a).left :=
      funext fun z => by rw [hB, Over.comp_left]
    rw [e1] at d2
    refine Mz.inj (Over.OverMorphism.ext ?_)
    rw [GlobalTheory.VerticalDeriv.isDerivAt0_unique d2 d1, hΦ, hΦ, hact a x, Over.comp_left, Category.assoc, Category.assoc,
      P.m.act]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', hc⟩ := hh x x'
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    have e1 : a' = ℓ (Φ x) := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      v' a' (hΦ x).symm hv' ha'
    have e2 : b' = ℓ (Φ x') := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      w' b' (hΦ x').symm hw' hb'
    rw [hc, e1, e2, ← (key A φ g' u Hm χ ℓ hφ hAH hℓ).2]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, -⟩ := hh 0 0
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    obtain ⟨MT, hMT, hI⟩ := hI
    have k2 : ∀ x (δ : P.τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i ↔
        Φ x = h fun a => (δ (β a) : ℂ) := fun x δ => by
      have a1 := t1 MT hMT ((Int.castAddHom ℂ).comp δ)
      constructor
      · intro hx
        refine Mz.inj (Over.OverMorphism.ext ?_)
        rw [hΦ, hx]
        exact a1.symm
      · intro hx
        refine Over.OverMorphism.ext (P.m.cart.1.hom_ext ?_ ?_)
        · rw [← hΦ, hx]
          exact a1
        · rw [Over.w (MV.pt x), Over.w (MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i)]
    have k3 : ∀ δ : P.τ.X →+ ℤ, h (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) • h fun a => (δ (β a) : ℂ) := fun δ => by
      rw [← map_smul]
      rfl
    rw [(key A φ g' u Hm χ ℓ hφ hAH hℓ).1, t3 A φ g' u ℓ hφ hℓ]
    constructor
    · rintro ⟨hp, z, rfl⟩
      obtain ⟨δ, rfl⟩ := (t2 z).1 hp
      refine ⟨Φ.symm (h fun a => (δ (β a) : ℂ)), (hI _).2 ⟨δ, (k2 _ δ).2 (Φ.apply_symm_apply _)⟩, ?_⟩
      rw [Φ.apply_symm_apply, k3]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨δ, hδ⟩ := (hI x).1 hx
      rw [(k2 x δ).1 hδ, ← k3]
      exact ⟨(t2 _).2 ⟨δ, rfl⟩, _, rfl⟩

theorem per_small (e : FamExp t.G M B ψ) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) (hB : B ∈ 𝓝 b₀) :
    ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.2 ∈ e.per bz.1 → bz.2 = 0 := by
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b₀ hb
  have hB' : ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.1 ∈ B :=
    (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually_mem hB
  have hc : Continuous fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, (0 : Fin g → ℂ)) := by fun_prop
  have hL0 := (hc.tendsto (b₀, 0)).eventually hL
  filter_upwards [hL, hL0, hB'] with bz h1 h2 h3 hper
  have h0 : e.ex bz.1 0 = 1 := by
    have h4 := e.add bz.1 h3 0 0
    rw [add_zero] at h4
    simpa using h4.symm
  have hx : e.ex bz.1 bz.2 = e.ex bz.1 0 := by
    rw [h0]
    exact hper
  rw [← h1, hx]
  exact h2

end LevelTowerAlt.Val
end
end
end
