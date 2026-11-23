module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
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
import Mathlib.RingTheory.Henselian
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmersedByOfLocalCoords

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.SecImm
open GlobalTheory.Points GlobalTheory.ProjSpace

section
variable {o : Type} [CommRing o] {m m' : ℕ} {K : Type} [Field K] {Y : Scheme.{0}}

theorem crd_toProj {L : LB Y} (f : Y ⟶ Sp o) (s : Fin (m + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (x : Sp K ⟶ Y) (k : L.ι) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    Crd (O1 o m) (coord o m) (x ≫ toProj f s hs) (fun i => valF x _ ((s i).f k)) := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (x ≫ toProj f s hs) (iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) := fun z hz => ⟨hi hz, hk hz⟩
  have hu := (isUnit_resG_sec (s i) k (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k)
    (inf_le_left.trans (toProj_preimage_chart f s hs i).le) inf_le_right).map (valMap x _ hT).hom
  rw [← valR_eq] at hu
  refine (LinFrame.crd_iff _ _).2 ⟨i, hu.unit, hi, fun j => ?_⟩
  have := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul f s hs i j k
    (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) inf_le_left inf_le_right)
  rw [valR_mul x _ hT, valR_res x _ hT, LinFrame.valR_pullRatio x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end

end GlobalTheory.ZH.SecImm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective

section

@[expose] public section

namespace GlobalTheory

theorem matrix_exists_left_inverse_of_field {K : Type} [Field K] {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) K) (h : Function.Injective Q.mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q' * Q = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' Q) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFlagEqOfPluckerPointsEqFieldPoints

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker.Sep

theorem initSpan_min {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {d : ℕ} (v : Fin d → N) (i : ℕ) :
    initSpan S v i = initSpan S v (min i d) := by
  unfold initSpan
  congr 2
  ext j
  simp only [Set.mem_setOf_eq, lt_min_iff, j.2, and_true]

theorem initSpan_cols_eq {K : Type} [Field K] {n d : ℕ} (P P' : Matrix (Fin n) (Fin d) K)
    (hP : LinearIndependent K (fun j r => P r j))
    (h : ∀ m : Fin d, ∃ u : Kˣ, ∀ r : Fin ((m : ℕ) + 1) → Fin n,
      (P'.submatrix r (Fin.castLE m.2)).det = u * (P.submatrix r (Fin.castLE m.2)).det)
    (i : ℕ) : initSpan K (fun j r => P' r j) i = initSpan K (fun j r => P r j) i := by
  rcases n with _ | N
  · exact Subsingleton.elim _ _
  rw [initSpan_min (fun j r => P' r j) i, initSpan_min (fun j r => P r j) i]
  rcases hmi : min i d with _ | m
  · unfold initSpan
    have e0 : {j : Fin d | (j : ℕ) < 0} = ∅ := Set.eq_empty_of_forall_notMem fun j hj => Nat.not_lt_zero _ hj
    rw [e0, Set.image_empty, Set.image_empty]
  have hm : m < d := by have := min_le_right i d; omega
  have hr : ∀ Q : Matrix (Fin (N + 1)) (Fin d) K, initSpan K (fun j r => Q r j) (m + 1) =
      Submodule.span K (Set.range fun l : Fin (m + 1) => (fun j r => Q r j) (Fin.castLE hm l)) := by
    intro Q
    unfold initSpan
    congr 1
    ext w
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨_, show ((Fin.castLE hm l : Fin d) : ℕ) < m + 1 from l.2, rfl⟩
  rw [hr, hr]
  obtain ⟨u, hu⟩ := h ⟨m, hm⟩
  have hind : LinearIndependent K fun l : Fin (m + 1) => (fun j r => P r j) (Fin.castLE hm l) :=
    hP.comp _ (Fin.castLE_injective _)
  refine (((GlobalTheory.FlagEmb.PlkSpan.main K N (m + 1) _ _).2 hind).2 ⟨u, ?_⟩).2
  funext q
  simp only [GlobalTheory.FlagEmb.plk, id, Pi.smul_apply, smul_eq_mul]
  have e : ∀ Q : Matrix (Fin (N + 1)) (Fin d) K, (Matrix.of fun l l' : Fin (m + 1) =>
      (fun j r => Q r j) (Fin.castLE hm l) (GlobalTheory.FlagEmb.plE N (m + 1) q l')) =
      (Q.submatrix (GlobalTheory.FlagEmb.plE N (m + 1) q) (Fin.castLE hm)).transpose := by
    intro Q; ext; rfl
  rw [e, e, Matrix.det_transpose, Matrix.det_transpose]
  exact hu _

end GlobalTheory.FlagPlucker.Sep

noncomputable section

namespace GlobalTheory.FlagPlucker.Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem initSpan_comp {S N N' : Type} [CommRing S] [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N']
    {d : ℕ} (L : N →ₗ[S] N') (v : Fin d → N) (i : ℕ) : initSpan S (L ∘ v) i = (initSpan S v i).map L := by
  unfold initSpan
  rw [Submodule.map_span, Set.image_comp]

theorem vecAt_eq_vec (F : Frames Y π) (Mc : MChart Y) (k : F.J) {S : Type} [CommRing S] (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hM : ⊤ ≤ x ⁻¹ᵁ Mc.U)
    (hzU : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    F.vecAt k z hz hx σ j = vec Mc x hM (fun r => (plkU F Mc k σ).map (ev z _ hzU) r j) := by
  subst hx
  have hh : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := le_preimage_inf hM (F.inM hz rfl)
  rw [Frames.vecAt, ← vec_chg Mc (F.M k).toMChart (z ≫ π) hM (F.inM hz rfl) hh]
  congr 1
  funext r
  rw [plkU, Matrix.map_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.map_apply]
  exact congrArg₂ (· * ·) (ev_appLE z π _ hzU hh _).symm (ev_res z _ hzU hz _).symm

theorem valF_plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) {K : Type} [Field K] (a : Sp K ⟶ T) (k : F.J)
    (hj : ⊤ ≤ a ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k)) (hU : ⊤ ≤ (a ≫ g) ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) :
    valF a _ (plkLoc F Mc g hg σ m (Fin.succ (Fintype.equivFin _ r)) (fun _ => k)) =
      (((plkU F Mc k σ).map (ev (a ≫ g) _ hU)).submatrix r (Fin.castLE m.2)).det := by
  have e : plkIdx Mc m (Fin.succ (Fintype.equivFin _ r)) = some r := by simp [plkIdx]
  simp only [plkLoc, e]
  rw [valF, dite_eq_left hj]
  show ev a _ hj ((g.appLE _ _ _).hom _) = _
  rw [ev_appLE a g _ hj hU, plkMinor, RingHom.map_det]
  rfl

end GlobalTheory.FlagPlucker.Sep

end

theorem GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (t : ∀ (σ : E →+* ℂ) (m : Fin (Dw.mult σ)), Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ σ m q, (t σ m q).f = plkLoc F Mc g hg σ m q) → ∀ (ht : ∀ σ m, ⨆ q, nonzeroLocus (t σ m q) = ⊤) {R : Type} [CommRing R] (f : T ⟶ Sp R) (K : Type) [Field K] (a a' : Sp K ⟶ T), a ≫ g ≫ π = a' ≫ g ≫ π → (∀ σ m, a ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m) = a' ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m)) → ∃ hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π, ∀ σ (i : ℕ), F.step (a' ≫ g) hx' σ i = F.step (a ≫ g) rfl σ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg t htf ht R _ f K _ a a' hπ hP
  have hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π := by simpa only [Category.assoc] using hπ.symm
  refine ⟨hx', fun σ i => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing F.cover (a ≫ g)
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing F.cover (a' ≫ g)
  have hM : ⊤ ≤ ((a ≫ g) ≫ π) ⁻¹ᵁ Mc.U := fun p _ => hg (Set.mem_univ (a p))
  have hM' : ⊤ ≤ ((a' ≫ g) ≫ π) ⁻¹ᵁ Mc.U := fun p _ => hg (Set.mem_univ (a' p))
  have hU : ⊤ ≤ (a ≫ g) ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U) := le_preimage_inf hk hM
  have hU' : ⊤ ≤ (a' ≫ g) ⁻¹ᵁ (F.U k' ⊓ π ⁻¹ᵁ Mc.U) := le_preimage_inf hk' hM'
  have e1 : F.vecAt k (a ≫ g) hk rfl σ =
      (vec Mc _ hM).toLinearMap ∘ fun j r => (plkU F Mc k σ).map (ev (a ≫ g) _ hU) r j :=
    funext fun j => Sep.vecAt_eq_vec F Mc k (a ≫ g) hk rfl hM hU σ j
  have e2 : F.vecAt k' (a' ≫ g) hk' hx' σ =
      (vec Mc _ hM).toLinearMap ∘ fun j r => (plkU F Mc k' σ).map (ev (a' ≫ g) _ hU') r j :=
    funext fun j => Sep.vecAt_eq_vec F Mc k' (a' ≫ g) hk' hx' hM hU' σ j
  rw [F.step_eq k' _ hk' hx', F.step_eq k _ hk rfl, e1, e2, Sep.initSpan_comp, Sep.initSpan_comp]
  congr 1
  refine Sep.initSpan_cols_eq _ _ ?_ ?_ i
  · have := F.linearIndependent_vecAt k (a ≫ g) hk rfl σ
    rw [e1] at this
    exact this.of_comp _
  · intro m
    have hj : ⊤ ≤ a ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k) := by
      exact fun p _ => Set.mem_iInter.2 fun _ => hk (Set.mem_univ p)
    have hj' : ⊤ ≤ a' ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k') := by
      exact fun p _ => Set.mem_iInter.2 fun _ => hk' (Set.mem_univ p)
    have c1 := GlobalTheory.ZH.SecImm.crd_toProj f (t σ m) (ht σ m) a _ hj
    have c2 := GlobalTheory.ZH.SecImm.crd_toProj f (t σ m) (ht σ m) a' _ hj'
    rw [← hP σ m] at c2
    obtain ⟨u, hu⟩ := GlobalTheory.ZH.CrdCalc.crd_unique c1 c2
    refine ⟨u, fun r => ?_⟩
    have e := hu (Fin.succ (Fintype.equivFin _ r))
    simp only [htf σ m] at e
    rw [Sep.valF_plkLoc F Mc g hg σ m a k hj hU r, Sep.valF_plkLoc F Mc g hg σ m a' k' hj' hU' r] at e
    exact e
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFlagEqOfPluckerPointsEqFieldPointsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (t : ∀ (σ : E →+* ℂ) (m : Fin (Dw.mult σ)), Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ σ m q, (t σ m q).f = plkLoc F Mc g hg σ m q) → ∀ (ht : ∀ σ m, ⨆ q, nonzeroLocus (t σ m q) = ⊤) {R : Type} [CommRing R] (f : T ⟶ Sp R) (K : Type) [Field K] (a a' : Sp K ⟶ T), a ≫ g ≫ π = a' ≫ g ≫ π → (∀ σ m, a ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m) = a' ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m)) → ∃ hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π, ∀ σ (i : ℕ), F.step (a' ≫ g) hx' σ i = F.step (a ≫ g) rfl σ i := by
  first | exact @GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | exact GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | (intros; apply GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq <;> assumption)
end
end
