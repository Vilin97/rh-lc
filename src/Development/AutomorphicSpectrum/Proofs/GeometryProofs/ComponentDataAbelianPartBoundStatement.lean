module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogIntSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToToStalk

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

end CoordInhab

end GlobalTheory.CompanionTheory.Ar
end
end
end

-- Source module: Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsRingHomComplex

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProvConj

open MeasureTheory _root_.Metric Filter Topology
open ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Regular hiding le_tmax tmax_le
open GroundTheory.Heights₂.Heights.LowerBoundFree ReciprocityTheory.ChartRestriction.G.Geo

section Ext

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

variable (B : BoundedPshData A) (j : Fin B.N) (V U : Set X) (hV : IsOpen V) (hU : IsOpen U) (hUV : closure U ⊆ V)
    (hVj : V ⊆ B.mid j)

end Ext

section HidaSetting

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d}
  {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ}

end HidaSetting

section Main

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]




end Main

section Points

open MvPolynomial GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_scaled_eq_zero (y : (Σ k, ι k) → Ω) (T : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => y p * T p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h : ∀ f : MRing ι, aeval (fun p : Σ k, ι k => y p * T p.1) f = eval T (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  rw [h, h0, map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem y_ne_of_X_notMem (y : (Σ k, ι k) → Ω) {p : Σ k, ι k} (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem exists_bound (F : MRing ι) : ∃ M : ℕ, ∀ M', M ≤ M' → ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M' := by
  classical
  refine ⟨∑ m ∈ F.support, ∑ p, m p, fun M' hM' m hm k => le_trans ?_ hM'⟩
  calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
        Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = ∑ p, m p := (Fintype.sum_sigma _).symm
    _ ≤ _ := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm

theorem valAt_ne_zero {y : (Σ k, ι k) → Ω} {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (h : IsVerticalDivisorAt (mCoordIdeal y) p b f g) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hP : IsMultiHomogIdeal (mCoordIdeal y)) :
    valAt y (aeval y f / aeval y g * chartMono y c (-b)) z ≠ 0 := by
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_of_X_notMem y fun hX => hc k (by simpa using hz.2 _ hX)
  set z' : (Σ k, ι k) → ℂ := fun q => (z ⟨q.1, c q.1⟩)⁻¹ * z q with hz'
  set y' : (Σ k, ι k) → Ω := fun q => y q * (y ⟨q.1, c q.1⟩)⁻¹ with hy'
  have hz'P : z' ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul hP (fun k => (z ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) hz
  have hz1 : ∀ k, z' ⟨k, c k⟩ = 1 := fun k => inv_mul_cancel₀ (hc k)
  have hy1 : ∀ k, y' ⟨k, c k⟩ = 1 := fun k => mul_inv_cancel₀ (hyc k)
  obtain ⟨u, v, hu, hv, huv⟩ := h.unit_off_fibre (RingHom.ker (aeval z' : MRing ι →ₐ[ℤ] ℂ)) (RingHom.ker_isPrime _)
    (fun a ha => by rw [RingHom.mem_ker, ← eval_map_int]; exact hz'P.2 a ha)
    (fun k => ⟨c k, by simp [RingHom.mem_ker, hz1]⟩) (by simpa [RingHom.mem_ker] using hp)
  rw [RingHom.mem_ker] at hu hv
  obtain ⟨Mu, hMu⟩ := exists_bound u
  obtain ⟨Mv, hMv⟩ := exists_bound v
  have hU := homogAt_isMultiHomog c (Mu + Mv) u (hMu _ (by omega))
  have hV := homogAt_isMultiHomog c (Mu + Mv) v (hMv _ (by omega))
  have sy : ∀ q : Σ k, ι k, y q = y ⟨q.1, c q.1⟩ * y' q := fun q => by
    simp only [hy']; field_simp [hyc q.1]
  have sz : ∀ q : Σ k, ι k, z q = z ⟨q.1, c q.1⟩ * z' q := fun q => by
    simp only [hz']; field_simp [hc q.1]
  have eU := aeval_scale hU (fun k => z ⟨k, c k⟩) z' z sz
  have eV := aeval_scale hV (fun k => z ⟨k, c k⟩) z' z sz
  have eU' := aeval_scale hU (fun k => y ⟨k, c k⟩) y' y sy
  have eV' := aeval_scale hV (fun k => y ⟨k, c k⟩) y' y sy
  rw [aeval_homogAt c _ _ _ hz1] at eU eV
  rw [aeval_homogAt c _ _ _ hy1] at eU' eV'
  have hzp : (∏ k, z ⟨k, c k⟩ ^ (Mu + Mv)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hUz : aeval z (homogAt c (Mu + Mv) u) ≠ 0 := by rw [eU]; exact mul_ne_zero hzp hu
  have hVz : aeval z (homogAt c (Mu + Mv) v) ≠ 0 := by rw [eV]; exact mul_ne_zero hzp hv
  have hUy : aeval y (homogAt c (Mu + Mv) u) ≠ 0 := fun h0 =>
    hUz (by rw [← eval_map_int]; exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hU h0))
  obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
  have hgy : aeval y g ≠ 0 := fun h0 => h.den_not_mem (mem_mCoordIdeal_of_aeval_eq_zero y hg h0)
  have ef := aeval_scale hf (fun k => y ⟨k, c k⟩) y' y sy
  have eg := aeval_scale hg (fun k => y ⟨k, c k⟩) y' y sy
  have e0 : aeval y' (u * f - v * g) = 0 := aeval_scaled_eq_zero y (fun k => (y ⟨k, c k⟩)⁻¹) huv
  rw [map_sub, map_mul, map_mul] at e0
  have hm : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← hb]
    congr 1
    simp
  have hval : IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z
      (eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) v)) /
        eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) u))) := by
    refine ⟨_, _, _, hV, hU, hUy, ?_, by rwa [eval_map_int], rfl⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hgy, eU', eV', ef, eg, ← hm]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ (Mu + Mv)) * chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k) * e0
  rw [valAt_eq hz hval, eval_map_int, eval_map_int]
  exact div_ne_zero hVz hUz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

end Points

section Final

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

end Final

end GlobalTheory.CompanionTheory.Ar.ProvConj

namespace GlobalTheory.CompanionTheory.Ar.ProvParts

section An

open MeasureTheory _root_.Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
open GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

end PullTop

end An

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

end GlobalTheory.CompanionTheory.Ar.ProvParts
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBound

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

section Field

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L : Type} [Field L]

theorem centre_map (zL : Sp L ⟶ X) (e : L →+* ℂ) : centre (spMap e ≫ zL) = centre zL := by
  refine (Scheme.Hom.comp_apply (spMap e) zL _).trans ?_
  exact congrArg zL (Subsingleton.elim _ _)

theorem descend {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (zL : Sp L ⟶ X) (e : L →+* ℂ) {a : Ω} {r : ℂ}
    (h : ValAt ξ (spMap e ≫ zL) a r) : ∃ t : L, ValAt ξ zL a t ∧ e t = r := by
  have hc : centre zL = centre (spMap e ≫ zL) := (centre_map zL e).symm
  have h0 := h
  obtain ⟨h', s, hs, -⟩ := h
  have h'' : genPt ξ ⤳ centre zL := hc ▸ h'
  have hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s)) :=
    ⟨h'', _, (genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩
  exact ⟨_, hv, ValAt.unique hξ (valAt_of_field_map ξ zL _ e rfl hv) h0⟩

theorem coords_map (ξ : Sp Ω ⟶ X) {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {zL : Sp L ⟶ X}
    {w : (Σ k, J k) → L} (hw : CoordsAt ξ y zL w) (e : L →+* ℂ) :
    CoordsAt ξ y (spMap e ≫ zL) (fun p => e (w p)) := by
  refine ⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩
  have hne : w ⟨k, c⟩ ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨hy, hi⟩ := hw.2 k c (isUnit_iff_ne_zero.2 hne)
  refine ⟨hy, fun i => ?_⟩
  obtain ⟨ρ, hρ, hr⟩ := hi i
  exact ⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩

variable {ξ : Sp Ω ⟶ X} {z : Sp L ⟶ X}

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.2 hr)
  refine ⟨h1, (u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_, eq_inv_of_mul_eq_one_left ?_⟩
  · rw [← map_mul, Units.inv_mul, map_one]
  · refine ((Scheme.stalkClosedPointTo z).hom.map_mul _ _).symm.trans ?_
    exact (congrArg (Scheme.stalkClosedPointTo z).hom (Units.inv_mul u)).trans (Scheme.stalkClosedPointTo z).hom.map_one

theorem val_pow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using RootHt.valAt_one h₀
  | succ n ih => simpa [pow_succ] using RootHt.valAt_mul ih h

theorem val_zpow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using val_pow h₀ h n
  | negSucc n =>
    simpa [zpow_negSucc] using val_inv (val_pow h₀ h (n + 1)) (pow_ne_zero _ hr)

theorem val_prod_zpow (h₀ : genPt ξ ⤳ centre z) {K : Type} (s : Finset K) {A : K → Ω} {r : K → L} (b : K → ℤ)
    (h : ∀ k, ValAt ξ z (A k) (r k)) (hr : ∀ k, r k ≠ 0) :
    ValAt ξ z (∏ k ∈ s, A k ^ b k) (∏ k ∈ s, r k ^ b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.valAt_one h₀
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact RootHt.valAt_mul (val_zpow h₀ (h k) (hr k) _) ih

end Field

theorem vertical_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  intro E _ _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or L _ _ z w cc p hw hcc hp
  classical
  obtain ⟨e₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have hT := Or.𝔐.tie
  have hξ := hT.gen
  have hwe := fun e : L →+* ℂ => coords_map Or.𝔐.ξ hw e
  have hm : ∀ e : L →+* ℂ, (fun q => e (w q)) ∈ mcPts (mCoordIdeal Dc.y) := fun e =>
    (GlobalTheory.T.complex_points_iff_centres _ _ _ K J _ hT _).2 ⟨_, Or.𝔐.all _, hwe e⟩
  have tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ),
      ValAt Or.𝔐.ξ (spMap e ≫ z) a r ↔ IsValueAt Dc.y a (fun q => e (w q)) r :=
    fun e a r => GlobalTheory.T.valAt_iff_value_at _ _ _ K J _ hT _ _ (Or.𝔐.all _) (hwe e) a r
  have hne := GlobalTheory.CompanionTheory.Ar.ProvConj.valAt_ne_zero (Dc.S_prime p hp).ne_zero (Dc.vertical p hp) (hm e₀) cc
    (fun k => (map_ne_zero e₀).2 (hcc k)) Dc.arith.2.1.2.1
  have hex : ∃ v, IsValueAt Dc.y (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p)) (fun q => e₀ (w q)) v := by
    by_contra h
    exact hne (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_right h])
  obtain ⟨v, hv⟩ := hex
  rw [valAt_eq (hm e₀) hv] at hne
  obtain ⟨t, ht, het⟩ := descend hξ z e₀ ((tv e₀ _ _).2 hv)
  refine ⟨t, fun h0 => hne (by rw [← het, h0, map_zero]), ht, fun e => ?_⟩
  have hve := valAt_of_field_map Or.𝔐.ξ z _ e rfl ht
  have hccz : ∀ k, e (w ⟨k, cc k⟩) ≠ 0 := fun k => (map_ne_zero e).2 (hcc k)
  have hc : ∃ c : (k : K) → J k, ∀ k, (fun q => e (w q)) ⟨k, c k⟩ ≠ 0 := ⟨cc, hccz⟩
  unfold ComponentData.vertFactor
  rw [dite_eq_left hc]
  have hcs := hc.choose_spec
  generalize hc.choose = c at hcs ⊢
  have hcs' : ∀ k, e (w ⟨k, c k⟩) ≠ 0 := hcs
  have hy : ∀ k, Dc.y ⟨k, c k⟩ ≠ 0 := fun k => ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).1
  have hy' : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0 := fun k => ((hwe e).2 k (cc k) (isUnit_iff_ne_zero.2 (hccz k))).1
  have hr : ∀ k, ValAt Or.𝔐.ξ (spMap e ≫ z) (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩)
      (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) := fun k => by
    obtain ⟨ρ, h1, h2⟩ := ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).2 (cc k)
    have h3 : e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩) = ρ := by
      rw [div_eq_iff (hcs' k)]
      exact h2
    rw [h3]
    exact h1
  have hall := RootHt.valAt_mul hve (val_prod_zpow (Or.𝔐.all _) Finset.univ (Dc.vdeg p) hr
    (fun k => div_ne_zero (hccz k) (hcs' k)))
  have ha : MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p) * ∏ k, (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) ^ Dc.vdeg p k =
      MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
        chartMono Dc.y c (-Dc.vdeg p) := by
    rw [_root_.mul_assoc]
    congr 1
    unfold chartMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, _root_.zpow_neg, _root_.zpow_neg, div_zpow, div_eq_mul_inv, ← _root_.mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ (hy' k)), _root_.one_mul]
  rw [ha] at hall
  rw [valAt_eq (hm e) ((tv e _ _).1 hall), ← norm_mul]
  have hid : e t * (∏ k, (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) ^ Dc.vdeg p k) *
      zMono (fun q => e (w q)) c (Dc.vdeg p) = e t * ∏ k, e (w ⟨k, cc k⟩) ^ Dc.vdeg p k := by
    rw [_root_.mul_assoc]
    congr 1
    unfold zMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hcs' k)]
  rw [hid, norm_mul, norm_prod]
  simp only [norm_zpow]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.exists_val_at_vert_factor_eq_norm_mul_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value <;> assumption)
end
end
