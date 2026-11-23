module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitWedge
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSpecializeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineGeneratorGeometricStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullbackStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsAtFieldPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstVal

def constGerm {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))

theorem genMap_constGerm {X : Scheme.{0}} {Ω O : Type} [Field Ω] [CommRing O] (f : O →+* Ω)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom f)) (p : Cpt ξ) (o : O) :
    genMap ξ p (constGerm s p.1 o) = f o := by
  letI : Algebra O Ω := f.toAlgebra
  exact ConstReg.genMap_germ_const ξ s hs p o

theorem genMap_self {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X)
    (x : X.presheaf.stalk (genPt z)) :
    genMap z ⟨genPt z, specializes_rfl⟩ x = (Scheme.stalkClosedPointTo z).hom x := by
  have e₀ : X.presheaf.stalkSpecializes (specializes_rfl (x := genPt z)) ≫ Scheme.stalkClosedPointTo z =
      Scheme.stalkClosedPointTo z := by
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Category.id_comp _
  exact congrArg (fun q => q.hom x) e₀

def closedMap {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X) :
    X.presheaf.stalk (centre z) →+* F :=
  (Scheme.stalkClosedPointTo z).hom

theorem closedPoint_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) :
    closedMap z (constGerm s (centre z) o) = f o :=
  (genMap_self z _).symm.trans (genMap_constGerm f z s hs ⟨genPt z, specializes_rfl⟩ o)

theorem isUnit_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) (ho : f o ≠ 0) :
    IsUnit (constGerm s (centre z) o) := by
  have h1 : IsUnit (closedMap z (constGerm s (centre z) o)) := by
    rw [closedPoint_constGerm f z s hs o]
    exact ho.isUnit
  haveI : IsLocalHom (closedMap z) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  exact isUnit_of_map_unit (closedMap z) _ h1

theorem map_frac {A L K O : Type} [CommRing A] [CommRing L] [Field K] [CommRing O] (β : O →+* K) (g : O → A)
    (φ : A →+* L) (e : K →+* L) (h : ∀ o, φ (g o) = e (β o)) {a b : O} {k : K} (hk : k * β b = β a)
    (u : Aˣ) (hu : (u : A) = g b) : φ (g a * ↑u⁻¹) = e k := by
  have hw : e (β b) * φ ↑u⁻¹ = 1 := by
    rw [← h b, ← hu, ← map_mul, u.mul_inv, map_one]
  rw [map_mul, h a, ← hk, map_mul, _root_.mul_assoc, hw, _root_.mul_one]

theorem valAt_of_frac {X : Scheme.{0}} {K Ω F O : Type} [Field K] [Field Ω] [Field F] [CommRing O]
    (β : O →+* K) (inc : K →+* Ω) (βF : K →+* F)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of F) ⟶ X)
    (s : X ⟶ Spec (CommRingCat.of O))
    (hξ : ξ ≫ s = Spec.map (CommRingCat.ofHom (inc.comp β)))
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom (βF.comp β)))
    (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (h : genPt ξ ⤳ centre z) (k : K) : ValAt ξ z (inc k) (βF k) := by
  obtain ⟨a, b, hb, hk⟩ := hfr k
  obtain ⟨u, hu⟩ := isUnit_constGerm (βF.comp β) z s hz b ((map_ne_zero βF).2 hb)
  have e₁ : genMap ξ ⟨centre z, h⟩ (constGerm s (centre z) a * ↑u⁻¹) = inc k :=
    map_frac β (constGerm s (centre z)) (genMap ξ ⟨centre z, h⟩) inc
      (fun o => genMap_constGerm (inc.comp β) ξ s hξ ⟨centre z, h⟩ o) hk u hu
  have e₂ : closedMap z (constGerm s (centre z) a * ↑u⁻¹) = βF k :=
    map_frac β (constGerm s (centre z)) (closedMap z) βF
      (fun o => closedPoint_constGerm (βF.comp β) z s hz o) hk u hu
  exact ⟨h, _, e₁, e₂⟩

theorem constants_compose_structure {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {R : Type} [CommRing R] (w : Sp R ⟶ Xo.XF c) (f : c.F →+* R) (hw : w ≫ pullback.snd _ _ = spMap f) :
    (w ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (f.comp β)) := by
  have h1 : (w ≫ Y.j) ≫ Y.s = (w ≫ pullback.snd _ _) ≫ spMap β := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  rw [h1, hw, CommRingCat.ofHom_comp, Spec.map_comp]

theorem valAt_inc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ βF y hfr hy hsp k
  exact valAt_of_frac β Z.inc βF (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) Y.s (constants_compose_structure Y _ _ Z.over_inc)
    (constants_compose_structure Y _ _ hy) hfr hsp k

end GlobalTheory.CompanionTheory.Ar.Flat.ConstVal
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsAtFieldPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.constants_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc | exact GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorFieldEmbedding

section

@[expose] public section

open NumberField Module

namespace GlobalTheory.CompanionTheory.TraceProj

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) : Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  rw [Ideal.mem_bot]
  exact hn

theorem sum_repr_smul_dual (E : Type) [Field E] [NumberField E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B D : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i))
    (hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0)
    (hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k))
    (a : 𝓞 E) (l : ι) :
    ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k = algebraMap (𝓞 E) E a * D l := by
  have hB' : ∀ k, algebraMap (𝓞 E) E a * B k = ∑ i, ((b.repr (a * b k) i : ℤ) : E) * B i := by
    intro k
    rw [hB k, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b k)]

    simp [map_sum, hB, zsmul_eq_mul]
  have hterm : ∀ k i, Algebra.trace ℚ E (D l * (((b.repr (a * b k) i : ℤ) : E) * B i)) =
      (b.repr (a * b k) i : ℚ) * (if i = l then 1 else 0) := by
    intro k i
    rw [← hD i l, Algebra.traceForm_apply, mul_left_comm,
      show (((b.repr (a * b k) i : ℤ) : E)) * (D l * B i) =
        (b.repr (a * b k) i : ℚ) • (D l * B i) by rw [Rat.smul_def]; push_cast; rfl,
      LinearMap.map_smul, smul_eq_mul]
  have hcoord : ∀ k, D.repr (algebraMap (𝓞 E) E a * D l) k = (b.repr (a * b k) l : ℚ) := by
    intro k

    rw [hrepr, Algebra.traceForm_apply, mul_comm (algebraMap (𝓞 E) E a) (D l), mul_assoc, hB' k,
    Finset.mul_sum, map_sum]
    simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k
      = ∑ k, D.repr (algebraMap (𝓞 E) E a * D l) k • D k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcoord, Rat.smul_def]
        push_cast
        rfl
    _ = algebraMap (𝓞 E) E a * D l := D.sum_repr _

theorem exists_coeff (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i)) :
    ∃ c : ι → K, ∑ k, c k * σ (b k) = 1 ∧
      ∀ (a : 𝓞 E) (l : ι), ∑ k, ((b.repr (a * b k) l : ℤ) : K) * c k = σ a * c l := by
  have hnd := traceForm_nondegenerate ℚ E
  let D := (Algebra.traceForm ℚ E).dualBasis hnd B
  have hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hnd B j i
  have hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k) := fun x k =>
    LinearMap.BilinForm.dualBasis_repr_apply hnd B x k
  let σ' : E →+* K := IsFractionRing.lift (injective_of_charZero E K σ)
  have hσ' : ∀ x, σ' (algebraMap (𝓞 E) E x) = σ x := IsFractionRing.lift_algebraMap _
  have h1 : ∑ k, D k * B k = 1 := by
    have h0 : ∑ k, D k * B k - 1 = 0 := by
      refine hnd.1 _ fun x => ?_

      rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
      Algebra.trace_eq_matrix_trace D x, Matrix.trace]
      simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrepr, Algebra.traceForm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    exact sub_eq_zero.mp h0
  refine ⟨fun k => σ' (D k), ?_, fun a l => ?_⟩
  · calc ∑ k, σ' (D k) * σ (b k) = σ' (∑ k, D k * B k) := by simp [map_sum, hB, hσ']
      _ = 1 := by rw [h1, map_one]
  · have h := congrArg σ' (sum_repr_smul_dual E b B D hB hD hrepr a l)

    simpa [map_sum, map_mul, hσ'] using h

theorem exists_eigen_projector : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧
      ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L)
        (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W),
        ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  intro E _ _ K _ _ σ
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_coeff E K σ b (integralBasis E) (fun i => integralBasis_apply E i)
  let eqv := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun k => b (eqv.symm k), fun k => c (eqv.symm k), ?_, ?_⟩
  · rw [← hc1]
    exact Equiv.sum_comp eqv.symm (fun i => c i * σ (b i))
  · intro L W _ _ _ j ρ a w
    rw [Equiv.sum_comp eqv.symm (fun i => j (c i) • ρ (b i) w)]
    have hmul : ∀ i, ρ a (ρ (b i) w) = ∑ l, ((b.repr (a * b i) l : ℤ) : L) • ρ (b l) w := by
      intro i
      rw [← Module.End.mul_apply, ← map_mul]
      conv_lhs => rw [← b.sum_repr (a * b i)]

      simp [map_sum, LinearMap.sum_apply, Int.cast_smul_eq_zsmul]
    have hj : ∀ l, ∑ i, j (c i) * ((b.repr (a * b i) l : ℤ) : L) = j (σ a) * j (c l) := by
      intro l
      have h := congrArg j (hc2 a l)

      simp only [map_sum, map_mul, map_intCast] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

    simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, hj l]

end GlobalTheory.CompanionTheory.TraceProj
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorFieldEmbeddingStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.eigen_projector_field_embedding : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧ ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L) (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W), ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  first | exact @GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | exact GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | (intros; apply GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

theorem exchange {F W : Type} [Field F] [AddCommGroup W] [Module F W] {n : ℕ} {t u : Fin n → W}
    (ht : LinearIndependent F t) (h : Submodule.span F (Set.range t) = Submodule.span F (Set.range u)) :
    LinearIndependent F u ∧ ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, t i = ∑ k, A i k • u k) ∧ IsUnit A.det := by
  have hu : LinearIndependent F u := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have := linearIndependent_iff_card_eq_finrank_span.1 ht
    rw [Set.finrank, ← h]
    exact this
  refine ⟨hu, ?_⟩
  have h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose A hA using h1
  choose B hB using h2
  have hAB : (Matrix.of A) * (Matrix.of B) = 1 := by
    ext i l
    have key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0 := by
      have e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i := by
        conv_rhs => rw [← hA i]
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      have e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i := by
        simp [Matrix.one_apply]
      simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
    have := Fintype.linearIndependent_iff.1 ht _ key l
    exact sub_eq_zero.1 this
  refine ⟨Matrix.of A, fun i => (hA i).symm, ?_⟩
  have := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_value_frame (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U)
    (hβ : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (τ : E →+* ℂ) (F : Type) [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (n : ℕ) (b : Fin n → Z.V)
    (hb : (Z.eig τ).IsFrameAt b ⟨centre (y ≫ Y.j), h⟩) (v : Vecs y n)
    (hv : IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v) :
    ∃ (v₀ : Vecs y n) (A : Matrix (Fin n) (Fin n) F),
      IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v₀ ∧
      (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v₀ i) v') ∧
      (∀ i, IsComb (A i) v₀ (v i)) ∧ IsUnit A.det := by
  obtain ⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩ := GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y F y
  obtain ⟨m, e, cf, h1, h2⟩ := GlobalTheory.T.eigen_projector_field_embedding E c.F (tauIn c τ)
  obtain ⟨u, hval, hspan⟩ := GlobalTheory.T.lie_model_action_specialize Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF
    (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ hy h) h1
    (h2 Z.Ω Z.V Z.inc Z.ρ) hb
  choose t ht using fun i => Mu.onto _ (hv.1 i).1
  have hvt : v = fun i => Mu.pt (t i) := funext fun i => (ht i).symm
  subst hvt
  obtain ⟨hti, hts⟩ := (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv
  obtain ⟨hui, A, hA, hAu⟩ := exchange hti (hts.trans hspan.symm)
  refine ⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩,
    fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩

theorem valAt_mul {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, hu, rfl⟩ := ha
  obtain ⟨_, w, hw, rfl⟩ := hb
  exact ⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩

theorem valAt_eq {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

theorem exists_eq_smul_wedge {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {x : Cpt ξ} {p : ℕ} {f : Fin p → V}
    (hf : L.IsFrameAt f x) {α : Ω} {a : ⋀[Ω]^p V} (hα : α ≠ 0)
    (hL : L.wedge p x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ g₀ : Ω, a = g₀ • exteriorPower.ιMulti Ω p f := by
  have hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x :=
    Submodule.subset_span ⟨f, fun i => by
      rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  have hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f := by
    rw [mul_smul]; exact hr
  have hne := WedgeFrame.wedge_ne_zero f hf.1
  have h0 : (r : Ω) * α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr'; exact hne hr'.symm
  exact ⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

namespace GlobalTheory.CompanionTheory.Ar.Flat

open RepScalar

theorem exists_const_of_flatOnModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'
  obtain ⟨-, a, b, hgen, hrep⟩ := hfl
  obtain ⟨-, a', b', hgen', hrep'⟩ := hfl'
  obtain ⟨x, s, t, hx, ht, hst, ha', hb'⟩ := GlobalTheory.T.line_generator_geometric E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'
  refine ⟨x, hx, fun F _ βF y v w hf => ?_⟩
  obtain ⟨hy, hU, hv, hw⟩ := id hf
  have hpt : y (IsLocalRing.closedPoint F) ∈ U := hU ⟨_, rfl⟩
  have hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := ((Z.closure _).1 hpt).map Y.j.continuous
  have hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨U₁, hU₁, b₁, -, hb₁⟩ := h1 _ hmem
  obtain ⟨U₂, hU₂, b₂, -, hb₂⟩ := h2 _ hmem
  have f₁ := hb₁ _ hmem hU₁
  have f₂ := hb₂ _ hmem hU₂
  obtain ⟨v₀, A, hv₀, hval₁, hA, hAu⟩ := exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv
  obtain ⟨w₀, B, hw₀, hval₂, hB, -⟩ := exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw
  have hf₀ : IsFramed U τ βF y v₀ w₀ := ⟨hy, hU, hv₀, hw₀⟩
  obtain ⟨-, hb0, hco⟩ := hgen
  obtain ⟨α, κ, hα, hκ, hWa, hWb, -⟩ := hco _ hmem
  obtain ⟨ga, hga⟩ := exists_eq_smul_wedge f₁ hα hWa
  obtain ⟨gb, hgb⟩ := exists_eq_smul_wedge f₂ hκ hWb
  have hgb0 : gb ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hgb, zero_smul])
  have r1 := hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂
  have r2 := hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul])
    (by rw [hb', hgb, smul_smul]) hval₁ hval₂
  have r3 := valAt_mul (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1
  have e : s * ga / (t * gb) = Z.inc x * (ga / gb) := by
    rw [hst]; field_simp
  rw [e] at r2
  have e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀ := valAt_eq Z.gen r2 r3
  have c1 := hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  have c2 := hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  refine hAu.mul_left_injective ?_
  show φ' F y v w * A.det = βF x * φ F y v w * A.det
  rw [c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end
