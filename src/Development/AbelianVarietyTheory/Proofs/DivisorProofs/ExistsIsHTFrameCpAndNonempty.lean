module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FlagBasis

theorem exists_coeff {C U : Type} [Field C] [AddCommGroup U] [Module C U] {n : ℕ} (b : Fin n → U) (i : ℕ)
    {y : U} (hy : y ∈ step C b i) : ∃ r : Fin n → C, (∀ j : Fin n, i ≤ j → r j = 0) ∧ ∑ j, r j • b j = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun j hj => Pi.single_eq_of_ne ?_ _, by simp [Pi.single_apply]⟩
    rintro rfl
    exact absurd hk (not_lt.2 hj)
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a • r, fun j hj => by simp [hr j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem exists_lift {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {La : Submodule O U} (hfg : La.FG)
    {b : Fin n → U} (hb : LinearIndependent C b) (i : Fin n) {a : C} (ha : a ≠ 0) (hLa : a • b i ∈ La) :
    ∃ (w : U) (c : C), c ≠ 0 ∧ w ∈ La ∧ w - c • b i ∈ step C b i ∧
      ∀ x ∈ La, x ∈ step C b (i + 1) → ∃ o : O, x - o • w ∈ step C b i := by
  obtain ⟨c, hc, e, -⟩ := exists_grAt_eq hv hfg b i (hb.notMem_span_image (by simp)) ha
    (Submodule.zero_mem _) (by rwa [add_zero])
  obtain ⟨w, hw, hw'⟩ : c • (step C b i).mkQ (b i) ∈ grAt C La b i :=
    e ▸ Submodule.mem_span_singleton_self _
  have hw'' : (step C b i).mkQ w = c • (step C b i).mkQ (b i) := hw'
  refine ⟨w, c, hc, hw.1, (Submodule.Quotient.eq _).1 hw'', fun x hx hx' => ?_⟩
  have h1 : (step C b i).mkQ x ∈ grAt C La b i := ⟨x, ⟨hx, hx'⟩, rfl⟩
  rw [e, ← hw''] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨o, (Submodule.Quotient.eq _).1 ho.symm⟩

theorem exists_adapted_basis : ∀ (O C U : Type) [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (v : Valuation C ℝ≥0), v.Integers O → ∀ (n : ℕ) (La : Submodule O U), La.FG → ∀ b : Fin n → U, LinearIndependent C b → (∀ j, ∃ a : C, a ≠ 0 ∧ a • b j ∈ La) → ∃ g : Matrix (Fin n) (Fin n) C, (∀ i j, i < j → g i j = 0) ∧ (∀ i, g i i ≠ 0) ∧ IsLatBasis C La fun i => ∑ j, g i j • b j := by
  intro O C U _ _ _ _ _ _ _ v hv n La hfg b hb hLa
  classical
  choose a ha hLa using hLa
  choose w c hc hw hwb hgen using fun i => exists_lift hv hfg hb i (ha i) (hLa i)
  choose r hr hrb using fun i => exists_coeff b _ (hwb i)
  let g : Matrix (Fin n) (Fin n) C := fun i j => r i j + if j = i then c i else 0
  have hg : ∀ i j, i < j → g i j = 0 := fun i j h => by
    simp [g, hr i j h.le, h.ne']
  have hd : ∀ i, g i i ≠ 0 := fun i => by simpa [g, hr i i le_rfl] using hc i
  have hgw : (fun i => ∑ j, g i j • b j) = w := funext fun i => by
    simp [g, add_smul, Finset.sum_add_distrib, hrb]
  have hws : ∀ i : Fin n, w i ∈ step C b (i + 1) := fun i => by
    simpa using Submodule.add_mem _ (step_mono b (Nat.le_succ _) (hwb i))
      (Submodule.smul_mem _ (c i) (mem_step_succ b i))
  refine ⟨g, hg, hd, ?_, ?_⟩
  · have hu : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ fun i j hij => hg i j hij]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
    exact (Matrix.linearIndependent_rows_iff_isUnit.2 hu).map' (Fintype.linearCombination C b)
      (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hb s t h))
  · rw [hgw]
    refine le_antisymm (le_inf (Submodule.span_le.2 (Set.range_subset_iff.2 hw))
      (Submodule.span_le_restrictScalars O C _)) ?_
    have key : ∀ k, k ≤ n → ∀ x ∈ La, x ∈ step C b k → x ∈ Submodule.span O (Set.range w) := by
      intro k
      induction k with
      | zero =>
        intro _ x _ hx
        rw [step_zero, Submodule.mem_bot] at hx
        exact hx ▸ Submodule.zero_mem _
      | succ k ih =>
        intro hk x hx hx'
        obtain ⟨o, ho⟩ := hgen ⟨k, hk⟩ x hx hx'
        have h1 := ih (Nat.le_of_succ_le hk) _ (La.sub_mem hx (La.smul_mem o (hw _))) ho
        simpa using Submodule.add_mem _ h1
          (Submodule.smul_mem _ o (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
    rintro x ⟨hx, hx'⟩
    exact key n le_rfl x hx (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
      step_mono b (Nat.succ_le_of_lt i.2) (hws i)) hx')

end GlobalTheory.CompHt.FlagBasis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_polAV_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S X : Scheme.{0}} {t : SAB H S} {u : SAB H X} {x : S ⟶ X} (m : SABMap t u x) (hp : IsProper u.G.hom)
    (ha : RelAmple u.G u.PP.L) (hk : KTriv u.G u.PP.L) {C : Type} [Field C] (y : Sp C ⟶ S) :
    letI := H.starRing
    ∃ (A : PolAV (Sp C)) (oA : A.OAct (𝓞 E)) (φ : A.A.left ⟶ t.G.left), IsGrpPullback A.A t.G y φ ∧
      (∀ a, (oA.act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧ LBIso A.L (u.PP.L.pull (φ ≫ m.φ)) := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull y t
  generalize (⟨(Over.pullback y).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨w, g, -⟩ := n.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (y ≫ x) (IsLocalRing.closedPoint C)) trivial
  have hy : ∀ z, (y ≫ x) z ∈ U := fun z =>
    (congrArg (fun V => z ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (y ≫ x) hc)).mpr trivial
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hp
  have hA' := relAmple_pull n.cart.1 u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy ha
  have hK' := kTriv_pull n.cart u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hk
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hL : LBIso t'.PP.L (u.PP.L.pull (m₁.φ ≫ m.φ)) := hn ▸ ⟨w, g⟩
  exact ⟨GenericPol.toPolAV t' d hd hp' hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, m₁.φ, m₁.cart,
    m₁.act, hL⟩

theorem exists_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → v.Integers O → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O), (∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) → ∃ (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ hpO _ _ _ _ inst hstar hv T io y₀ hy k kO hk
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨G, t', m₁, m₂, -⟩ := y₀.2.2
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  have hinj : Function.Injective ((algebraMap O C).comp kO) := fun a b h => by
    simp only [RingHom.comp_apply, hk] at h
    exact IsFractionRing.injective T.V T.Fr (k.injective h)
  have hp0 : ∀ {R : Type} [CommRing R] (f : R →+* O), (p : R) ≠ 0 := fun f h =>
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : C) ≠ 0) (by
      rw [← map_natCast ((algebraMap O C).comp f), h, map_zero])
  have hpu : ∀ {R : Type} [CommRing R] (f : R →+* O), ¬ IsUnit (p : R) := fun f h =>
    hpO.out (by simpa using h.map f)
  haveI : IsLocalHom kO := ⟨fun a ha => by
    by_contra hau
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hu
      exact hau (hu ▸ u.isUnit)
    rw [hu, map_mul, map_pow] at ha
    have h1 : IsUnit (kO ϖ) := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
    obtain ⟨n', u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 kO) hϖ
    refine hpO.out ?_
    rw [← map_natCast kO, hu', map_mul, map_pow]
    exact (u'.isUnit.map kO).mul (h1.pow _)⟩
  obtain ⟨T', φ', G', m, hi, hf, -, -, U, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  obtain ⟨f', -, hf'⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ' hi hf.to_isIntegral kO hinj
  have hI : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal T'.V ^ n, f' a ∈ Ideal.span {(p : O)} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 f') hϖ
    refine ⟨n, fun a ha => ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨f' (b * ↑u⁻¹), ?_⟩
    rw [← map_natCast f', ← map_mul, hu, _root_.mul_assoc, Units.inv_mul_cancel_left]
  obtain ⟨A, oA, φ, hφ, hφa, hL⟩ :=
    exists_polAV_fibre m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (spMap k)
  have e1 : spMap f' ≫ spMap φ' = spMap kO := by rw [spMap_spMap, hf']
  have e2 : spMap k ≫ spMap (algebraMap T.V T.Fr) = spMap ((algebraMap O C).comp f') ≫ spMap φ' := by
    rw [spMap_spMap, spMap_spMap, RingHom.comp_assoc, hf']
    exact congrArg _ (RingHom.ext fun a => (hk a).symm)
  have h2 : IsGrpPullback A.A G.G (spMap ((algebraMap O C).comp f') ≫ spMap φ') (φ ≫ m₂.φ) :=
    (hφ.comp m₂.cart).congr e2 rfl
  obtain ⟨j, hj1, hj2⟩ : ∃ j : A.A.left ⟶ G'.G.left, j ≫ m.φ = φ ≫ m₂.φ ∧
      j ≫ G'.G.hom = A.A.hom ≫ spMap ((algebraMap O C).comp f') :=
    ⟨m.cart.1.lift _ _ (h2.1.w.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  have hj : IsGrpPullback A.A G'.G (spMap ((algebraMap O C).comp f')) j :=
    m.cart.cancel (h2.congr rfl hj1.symm) hj2
  have hja : ∀ a, (oA.act a).left ≫ j = j ≫ (G'.act.toRingAct.act a).left := fun a => m.cart.1.hom_ext
    (by
      change _ = (j ≫ (G'.act.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, m.act, hj1, reassoc_of% hj1, reassoc_of% (hφa a), m₂.act])
    (by rw [Category.assoc, Category.assoc, Over.w, hj2, Over.w_assoc])
  obtain ⟨ε⟩ : Nonempty (Eps p C) := inferInstance
  obtain ⟨-, -, -, -, -, P, -, -, -, -, hA, -, -, -, -, π, -, hπ, -, -, -, hgen, hπa, -⟩ :=
    exists_point_of_unif U.U.toUnifPre G'.semi U.lin hv ε f' hI A oA j hj hja
  clear hja hφa hj
  clear oA
  subst hA
  refine ⟨P, φ ≫ m₁.φ, hk, G, t', m₁, m₂, π ≫ m.φ, φ, (hπ.comp m.cart).congr e1 rfl, fun a => ?_, hφ, ?_, rfl, hL⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (m.act a)
  · rw [← Category.assoc, eq_of_heq hgen, hj1]

end GlobalTheory.CompHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPointStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) → HTChar p v P.Gt := by
  first | exact @GlobalTheory.CompHt.htChar_of_pointOver | exact GlobalTheory.CompHt.htChar_of_pointOver | (intros; apply GlobalTheory.CompHt.htChar_of_pointOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem fg_htLat (P : Point p v O (𝓞 E)) (τ : E →+* ℂ) : (htLat c P τ).FG := by
  classical
  unfold htLat
  split_ifs
  · exact P.fg_latTQuot _ _
  · exact fg_inf P.integers P.fg_latT _

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_isHTFrame (hs : ∀ a : 𝓞 E, star a = H.bar a) (hv : v.Integers O) {T : CDVR} {io : c.F →+* T.Fr}
    (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) :
    ∃ y : FrPt Xo c C, IsHTFrame p v O y₀ k y := by
  classical
  letI := io.toAlgebra
  obtain ⟨P, ψ, hP⟩ := GlobalTheory.CompHt.exists_pointOver E H Dw l Xo c p C v O hs hv T io y₀ hy k.toRingHom kO hk
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c _ C k y₀.1
  obtain ⟨x, hx⟩ := GlobalTheory.CompHt.TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz
  have hli : ∀ τ, LinearIndependent C fun j => P.bLie (x τ j) := fun τ =>
    (GlobalTheory.CompHt.alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P (GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP)).2 _ (x τ)
      (GlobalTheory.CompHt.linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ))
  have hmem : ∀ τ j, P.bLie (x τ j) ∈ htLat c P τ := fun τ j =>
    wRec_le_htLat P τ ⟨⟨x τ j, (hx τ j).isEig hP (z.eig τ j)⟩, rfl⟩
  choose g hg0 hg1 hg2 using fun τ => GlobalTheory.CompHt.FlagBasis.exists_adapted_basis O C P.V v hv (Dw.mult τ) (htLat c P τ) (fg_htLat P τ)
    (fun j => P.bLie (x τ j)) (hli τ) fun j => ⟨1, one_ne_zero, by rw [one_smul]; exact hmem τ j⟩
  obtain ⟨y, hy', -⟩ := existsUnique_frChg E H Dw l Xo c C z g 1 fun τ => by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg0 τ i j hij]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hg1 τ i).isUnit
  exact ⟨y, (GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).1.2.2.2.2.1 C y, kO, P, ψ, z, hP, hz, g, _, x, hy', hg0,
    by simp, hx, hg2⟩

end General

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem exists_isHTFrameCp {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
      (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hy
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp io).toAlgebra
  letI := H.starRing
  obtain ⟨y, h⟩ := exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p]) (fun _ => rfl)
    (PadicComplexInt.integers p) y₀ hy { k with commutes' := fun _ => rfl } kO hk
  exact ⟨p, hp, _, _, y, h⟩

end GlobalTheory.CompHt
end
end
end
