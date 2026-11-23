module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPush
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVol
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeets
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRoots
public import Development.WeilBound.CoreStatements.VolumeEquality.HolNull
import Development.WeilBound.CoreStatements.VolumeEquality.LocInj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibreStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibreStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersionStatement
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceA
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Algebra.Azumaya.Basic
public import Development.WeilBound.CoreStatements.VolumeEquality.RootBr
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSetStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSetStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionaryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
public import Development.WeilBound.CoreStatements.VolumeEquality.PiecesOf
public import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.VolumeEquality.Pieces

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.OnePiece

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace One

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

theorem ext_int {F Ω : Type} [Field F] [NumberField F] [Field Ω] {f g : F →+* Ω}
    (h : f.comp (algebraMap (𝓞 F) F) = g.comp (algebraMap (𝓞 F) F)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem constClosed_of {F Ω₀ Ω₁ Ω₂ : Type} [Field F] [NumberField F] [Field Ω₀] [Field Ω₁] [Field Ω₂] [Algebra F Ω₀]
    (i : Ω₀ →+* Ω₁) (g : Ω₁ →+* Ω₂) (cst : F →+* Ω₂) (h : (g.comp i).comp (algebraMap F Ω₀) = cst)
    (halg : ∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) : ConstClosed F Ω₀ := by
  intro a ha
  haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h1 : IsAlgebraic ℤ a := ha.restrictScalars ℤ
  obtain ⟨x, hx⟩ := halg (i a) (h1.algHom i.toIntAlgHom)
  refine ⟨x, 1, one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  refine (g.comp i).injective ?_
  rw [← h] at hx
  exact hx.symm

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

end One

open SheetDecomposition.One

theorem onePiece : OnePiece := by
  intro hgiven E _ _ _ H D l Xo c Y sm j j' n B Ω₀ _ ξ₀ Ω₁ Ω₂ _ _ ξ₁ g cst U hloc hξ₀ hpt hover halg hU hUc κ
  classical
  obtain ⟨-, -, -, -, hRes, -⟩ := hgiven
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨i, hi⟩ := exists_factor ξ₁ hξ₀ (hpt ▸ specializes_rfl)
  haveI : CharZero Ω₂ := (RingHom.charZero_iff cst.injective).1 inferInstance
  haveI : CharZero Ω₀ := (g.comp i).charZero
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre c.F Y.X Y.s Ω₀ ξ₀ hξ₀
  letI : Algebra c.F Ω₀ := b.toAlgebra
  have hb : (g.comp i).comp b = cst := by
    refine ext_int (spMap_inj ?_)
    rw [← hover, ← hi, ← hF1, spMap_comp', spMap_comp', spMap_comp', ← hF2]
    simp only [Category.assoc, pullback.condition]
  have hcl : ConstClosed c.F Ω₀ := constClosed_of i g cst hb halg
  have hβ := int_frac c.F
  obtain ⟨hnoeth, X', f, d, W', jW, hiso, hjW, -, -, hsm, -⟩ := GlobalTheory.T.exists_resolution_generic_fibre hRes E H D l Xo c _ _ Y hβ
  haveI := Y.jQ_open
  haveI hpre : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    have h : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
    infer_instance
  have hsurj := GlobalTheory.T.stalk_surjective_open_immersion _ _ _ _ _ f W' jW Y.jQ hpre inferInstance hiso hjW
  haveI hopen : IsOpenImmersion (W'.ι ≫ f) := by rw [← hjW]; infer_instance
  have hrange : Set.range (W'.ι ≫ f) = Set.range Y.jQ := by
    rw [← hjW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (show Function.Surjective jW from jW.homeomorph.surjective), Set.image_univ]
  have hlift : ∀ (R : Type) [Field R] (z : Sp R ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))),
      centre z ∈ Set.range Y.jQ → ∃ z' : Sp R ⟶ W'.toScheme, z' ≫ W'.ι ≫ f = z := by
    intro R _ z hz
    refine ⟨IsOpenImmersion.lift (W'.ι ≫ f) z ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    have : q = IsLocalRing.closedPoint R := Subsingleton.elim (α := PrimeSpectrum R) _ _
    rw [hrange, this]
    exact hz
  obtain ⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  haveI hemb : IsPreimmersion (W'.ι ≫ π) := by
    rw [hπ, ← Category.assoc]
    infer_instance
  rw [← hπ] at hsurj
  rw [← hs'] at hsm
  have hsm' : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hπs : π ≫ Y.s = s' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [hπ, hs', Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨ξW, hξW⟩ := hlift Ω₀ ξF
    (genPt_mem_dense Y.jQ.opensRange hFg (by simpa using Y.jQ_dense))
  have h2 : (ξW ≫ W'.ι) ≫ π = ξ₀ := by
    rw [hπ, ← hF1, ← hξW]
    simp only [Category.assoc]
  have h3 : (ξW ≫ W'.ι) ≫ s' = spMap (algebraMap c.F Ω₀) := by
    refine Eq.trans ?_ hF2
    rw [hs', ← hξW]
    simp only [Category.assoc]
  have hgW : genPt (ξW ≫ W'.ι) ∈ W' := (genPt ξW).2
  have hξg : IsCptGen (ξW ≫ W'.ι) := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ π s' hsm' h2 hξ₀ (hsurj _ hgW)
  have hab : ∀ x : Sp ℂ ⟶ X', ⊤ ≤ x ⁻¹ᵁ W' → centre (x ≫ π) ∈ abLocus Y.t.G := by
    intro x hx
    have h1 : f (centre x) ∈ Set.range Y.jQ := by
      rw [← hrange]
      exact ⟨⟨centre x, GagaRat.centre_mem hx⟩, rfl⟩
    rw [← Y.ab_gen] at h1
    rw [hπ]
    exact h1
  have hexF : ∀ x : Sp ℂ ⟶ X', ∃ r : ℂ, r ≠ 0 ∧ ∀ k, ∀ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t →
      r = (((k : ℕ) + 1 : ℕ) : ℂ) := by
    intro x
    by_cases h : ∃ k, ∃ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t
    · obtain ⟨k, t, ht, e⟩ := h
      refine ⟨(((k : ℕ) + 1 : ℕ) : ℂ), Nat.cast_ne_zero.2 (Nat.succ_ne_zero _), fun k' t' ht' e' => ?_⟩
      rw [B.disj k k' t ht t' ht' (e.symm.trans e')]
    · exact ⟨1, one_ne_zero, fun k t ht e => absurd ⟨k, t, ht, e⟩ h⟩
  choose F _ hF using hexF
  have hconst := const_of_hol κ s' (ξW ≫ W'.ι) W' F d hsm h3 hξg hcl (by
    intro m T y hT hc hy hW b₁ hb₁ b₂ hb₂
    obtain ⟨k₁, t₁, ht₁, e₁⟩ := B.onto _ (hab _ (hW b₁ hb₁))
    obtain ⟨k₂, t₂, ht₂, e₂⟩ := B.onto _ (hab _ (hW b₂ hb₂))
    rw [hF _ k₁ t₁ ht₁ e₁.symm, hF _ k₂ t₂ ht₂ e₂.symm,
      hloc m T (fun b => y b ≫ π) hT hc (GagaRat.isHolTo_comp π hy) (fun b hb => hab _ (hW b hb)) b₁ hb₁ b₂ hb₂ k₁ k₂
        t₁ ht₁ t₂ ht₂ e₁.symm e₂.symm])
  have hup : ∀ k, B.κ k = κ → ∀ t ∈ Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U → ∃ x : Sp ℂ ⟶ X',
      x ≫ π = B.pt k t ∧ x ≫ s' = spMap κ ∧ ⊤ ≤ x ⁻¹ᵁ W' ∧ genPt (ξW ≫ W'.ι) ⤳ centre x := by
    intro k hk t ht hu
    let z : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
      pullback.lift (B.pt k t) (spMap κ) (by rw [B.comp_s_eq_spMap_of_isOver k t ht, hk, spMap_comp'])
    have z1 : z ≫ pullback.fst _ _ = B.pt k t := pullback.lift_fst _ _ _
    have z2 : z ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
    obtain ⟨z', hz'⟩ := hlift ℂ z (by
      rw [← Y.ab_gen]
      have := B.interior k t ht
      rw [← z1] at this
      exact this)
    have a1 : (z' ≫ W'.ι) ≫ π = B.pt k t := by
      rw [hπ, ← z1, ← hz']
      simp only [Category.assoc]
    refine ⟨z' ≫ W'.ι, a1, ?_, GagaRat.top_le_of_centre_mem (centre z').2, ?_⟩
    · rw [hs', ← z2, ← hz']
      simp only [Category.assoc]
    · have a2 := hUc _ hu
      rw [← a1, ← h2, Category.assoc, Category.assoc] at a2
      have a3 : genPt ξW ⤳ centre z' := (W'.ι ≫ π).isEmbedding.isInducing.specializes_iff.1 a2
      exact a3.map W'.ι.continuous
  have hgU : genPt (ξW ≫ W'.ι) ∈ W' ⊓ π ⁻¹ᵁ U := by
    refine ⟨hgW, ?_⟩
    rw [← h2] at hU
    exact hU
  obtain ⟨x, hx, hxU⟩ := exists_point κ s' _ hgU
  obtain ⟨k, t, ht, e⟩ := B.onto _ (hab x fun q hq => (hxU hq).1)
  have hk : B.κ k = κ := by
    refine ext_int (spMap_inj ?_)
    rw [← B.comp_s_eq_spMap_of_isOver k t ht, e, Category.assoc, hπs, ← Category.assoc, hx, spMap_comp']
  have hu : ⊤ ≤ B.pt k t ⁻¹ᵁ U := by
    rw [e]
    exact fun q hq => (hxU hq).2
  refine ⟨k, ⟨hk, t, ht, hu⟩, ?_⟩
  rintro k' ⟨hk', t', ht', hu'⟩
  obtain ⟨x₁, a₁, b₁, c₁, d₁⟩ := hup k hk t ht hu
  obtain ⟨x₂, a₂, b₂, c₂, d₂⟩ := hup k' hk' t' ht' hu'
  have := hconst x₂ x₁ b₂ b₁ c₂ c₁ d₂ d₁
  rw [hF _ k t ht a₁, hF _ k' t' ht' a₂] at this
  exact Fin.ext (Nat.succ_injective (Nat.cast_injective this))

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.VolEqOf

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem degMu_eq (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj) (h7 : OnePiece)
    (hG : Top.Given) : ∃ κ : ℕ → ℕ → ℕ → ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E)
      (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
      (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type)
      [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd)
      (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ) (B : BaseUnif Y sm j j' n) (FF : Fin B.np → Set (Fin n → ℂ)) (v : ℝ)
      (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] (ξ₁ : Sp Ω₁ ⟶ Y.X) (g : Ω₁ →+* Ω₂) (cst : c.F →+* Ω₂),
      Or.sm = sm → Dc.j = j → Dc.j' = j' → Dc.n = n → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → B.Locc →
      (∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) → (∀ k, ∫ t in FF k, ballDens (B.F k).q t = v) → genPt ξ₁ = genPt Or.𝔐.ξ₀ →
      spMap g ≫ ξ₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → (∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) →
      degMu Hd = κ (Fintype.card (CMType H)) j j' * (Or.deg * Module.finrank ℚ c.F * v) := by
  classical
  obtain ⟨κ, -, hκ⟩ := transferU
  refine ⟨κ, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or sm j j' n B FF v Ω₁ Ω₂ _ _ ξ₁ g cst e1 e2 e3 e4 a1 a2 hL hF hv b1 b2 b3
  subst e1 e2 e3 e4
  obtain ⟨U, hU, hU', ⟨Z⟩⟩ := exists_sheets Or B h1 h2 h3 h4 h5 FF hF
  have h := hκ E H D Xo l c Y II K J Ω W Dc Hd S₀ Or (Z.pieces hG hF) (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) fun k => by
      simp only [one_mul]
      exact (GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E _ _ _ _ _ _ H (B.F k) (B.Γ k) (FF k) (B.arith k) (hF k) a1 a2).1
  refine h.trans (congrArg _ ?_)
  have := c.fin
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hu := h7 hG E H D l (Xo l) c Y _ _ _ _ B _ Or.𝔐.ξ₀ Ω₁ Ω₂ ξ₁ g cst U hL Or.𝔐.gen₀ b1 b2 b3 hU hU'
  have hc : (Finset.univ.filter fun k => ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U).card = Module.finrank ℚ c.F := by
    rw [← NumberField.Embeddings.card c.F ℂ, ← Finset.card_univ]
    refine Finset.card_bij (fun k _ => B.κ k) (fun _ _ => Finset.mem_univ _) (fun k hk k' hk' e => ?_) fun κ' _ => ?_
    · exact (hu (B.κ k')).unique ⟨e, (Finset.mem_filter.1 hk).2⟩ ⟨rfl, (Finset.mem_filter.1 hk').2⟩
    · obtain ⟨k, hk, -⟩ := hu κ'
      exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.2⟩, hk.1⟩
  show ∑ k : Fin B.np, (nSheets Or B U k : ℝ) * ∫ t in FF k, 1 * ballDens (B.F k).q t = _
  simp only [one_mul, hv, nSheets, Nat.cast_ite, Nat.cast_zero, ← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [← hc, mul_comm (Or.deg : ℝ)]

theorem volEq_of (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj) (h6 : BaseUnifEx2)
    (h7 : OnePiece) (h8 : BallVolEq) (h9 : DegPush) : Cmp.CmpSt → Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem),
      Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  intro hC hG E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hq hN
  obtain ⟨κ, hκ⟩ := degMu_eq h1 h2 h3 h4 h5 h7 hG
  obtain ⟨c₀, hc₀, hP⟩ := h9
  obtain ⟨B, hL⟩ := h6 hG E H D l (Xo l) c Y Sum.inr D.p D.q _ (by omega) (Or.inl ⟨rfl, rfl, rfl⟩) rfl
  obtain ⟨FF, hF⟩ := Classical.skolem.1 fun k =>
    GlobalTheory.T.exists_fundamental_set E _ _ _ _ _ _ (B.F k) (GlobalTheory.T.exists_group_dictionary E _ _ _ _ _ _ H (B.F k)).some _ (B.arith k)
  obtain ⟨v, hv⟩ : ∃ v, ∀ k, ∫ t in FF k, ballDens (B.F k).q t = v := by
    rcases isEmpty_or_nonempty (Fin B.np) with h | ⟨⟨k₀⟩⟩
    · exact ⟨0, h.elim⟩
    · exact ⟨_, fun k => h8 hG E H D l (Xo l) c Y _ B FF hq hN hF k k₀⟩
  have := c.fin
  have key : ∀ a, c₀ (Fintype.card (CMType H)) D.p D.q * T.vol a = κ (Fintype.card (CMType H)) D.p D.q * v := fun a => by
    obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, e1, e2, e3, e4, e5, e6⟩ := GlobalTheory.T.full_intersection_generic_bound hG Link.weilSt E H D Xo l c Y II hII hY
      (by omega) hq _ (o.Or 2 a).𝔐.ξ₀ (o.Or 2 a).𝔐.gen₀ T.bad ∅ false (fun p hp => ((o.bad_iff p).1 hp).1) (by simp) (by simp)
      fun p hp hd => (o.bad_iff p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩
    have eb : Or.bg = Sum.inl := e4
    have ej : Dc.j = D.p := e3
    have es : Or.sm = Sum.inr := by
      obtain ⟨τ⟩ : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
      refine Or.side.elim (fun h => h.2.1) fun h => ?_
      simpa [eb] using congrFun h.1 τ
    have eg : genPt (o.Fx a).ξf = genPt Or.𝔐.ξ₀ := by
      have g1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) ((o.Or 2 a).g_over.symm.trans (o.Or 2 a).𝔐.fn_over)
      rw [e1]
      exact ((congrArg (fun x => (o.Fx a).ξf x) (Subsingleton.elim (α := PrimeSpectrum (o.Fx a).Ωf) _ _)).trans g1).trans
        (congrArg (fun x => (o.Or 2 a).𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum (o.Or 2 a).𝔐.Ω₀) _ _))
    have ej' : Dc.j' = D.q := by have := Or.N_eq; unfold ComponentData.j'; omega
    have k1 := hκ E H D Xo l c Y II K J Ω W Dc Hd _ Or _ _ _ _ B FF v _ _ (o.Fx a).ξf (o.Or 2 a).g (o.Or 2 a).𝔐.cst es ej ej' Or.n_eq
      hq hN hL hF hv eg (by rw [← Category.assoc, ← (o.Or 2 a).g_over, Category.assoc, (o.Or 2 a).𝔐.cst_over]) (o.Or 2 a).g_const
    have k2 := hP GlobalTheory.T.agreement_positive GlobalTheory.T.proportional' hC hG (GlobalTheory.T.points_integrable_of_resolution_statement hG.2.2.2.2.1) E H D Xo l c Y T o II hY hX hII (by omega) hq
      (by omega) a K J Ω W Dc Hd Or eb es e5 ⟨fun p hp => e6 p (by simpa using hp), fun p hp => by simp [e2] at hp⟩ e2 eg.symm
    have hd : (Or.deg : ℝ) * Module.finrank ℚ c.F ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 Or.cover.1.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    exact mul_left_cancel₀ hd (by linear_combination k1 - k2)
  exact fun a a' => mul_left_cancel₀ (hc₀ _ _ _) ((key a).trans (key a').symm)

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.VolEqOfDegPush

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem SheetDecomposition.volEq_of_degPush (h : SheetDecomposition.DegPush) : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq :=
  SheetDecomposition.volEq_of SheetDecomposition.holNull SheetDecomposition.chartMeets SheetDecomposition.rootBranches SheetDecomposition.coverRoots SheetDecomposition.locInj SheetDecomposition.baseUnifEx2 SheetDecomposition.onePiece
    SheetDecomposition.ballVolEq h
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.VolEqOfIsFullIntersectionSystem

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem SheetDecomposition.volEq_of_isFullIntersectionSystem : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq :=
  SheetDecomposition.volEq_of_degPush SheetDecomposition.degPush
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  first | exact @SheetDecomposition.volEq_of_isFullIntersectionSystem | exact SheetDecomposition.volEq_of_isFullIntersectionSystem
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.T.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  exact @GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra
end
end
