module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ImageCptReflOfGenPt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeTieCompareStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatibleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentialsStatement
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntA
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MapDomainRelationLiftCommutingSquare

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem HostAut.s_symm_s (g : HostAut H) (a : 𝓞 E) : g.s (g.symm.s a) = a :=
  RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))

theorem HostAut.hostAut_symm_s_s (g : HostAut H) (a : 𝓞 E) : g.symm.s (g.s a) = a :=
  RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))

theorem HostAut.hostAut_refl_s (a : 𝓞 E) : (HostAut.refl H).s a = a :=
  RingOfIntegers.ext rfl

theorem oAct_eq {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] {u v : OAct O G}
    (h : ∀ a, u.act a = v.act a) : u = v := by
  cases u
  cases v
  have : ∀ a, _ = _ := h
  obtain rfl : _ = _ := funext this
  rfl

theorem twistSAB_eq_of_act {S : Scheme.{0}} (t : SAB H S) (g : HostAut H)
    (h : ∀ a, t.act.act (g.s a) = t.act.act a) : twistSAB t g = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct act g.s = act := oAct_eq h
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_twistSAB {S : Scheme.{0}} (t : SAB H S) (g g' : HostAut H)
    (h : ∀ a, g.s (g'.s a) = a) : twistSAB (twistSAB t g) g' = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct (twistAct act g.s) g'.s = act := oAct_eq fun a => congrArg act.act (h a)
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_symm_refl (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S) (g : HostAut H) :
    twistSAB (twistSAB t g) g.symm = t ∧ twistSAB (twistSAB t g.symm) g = t ∧
      twistSAB t (HostAut.refl H) = t :=
  ⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s,
    twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.AevalEqZeroOfMem

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.Sq

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    algHom_ext fun p => by simp [mConeMap]
  rw [← h, AlgHom.comp_apply, show mConeMap y f = 0 from hf, map_zero]

theorem valEq_of_lineIso {y : (Σ k, ι k) → Ω} (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {a b : K → ℤ} {f g : MRing ι}
    (h : IsLineIso (mCoordIdeal y) a b f g) : ValEq ℚ y a y b := by
  classical
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, hU⟩ := h
  have hne : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d → s ∉ mCoordIdeal y → aeval y s ≠ 0 := fun hs hP h0 =>
    hP (by rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hs, h0, map_zero, zero_mul])
  refine ⟨aeval y f / aeval y g, div_ne_zero (hne hf hfP) (hne hg hgP), fun O _ => ?_⟩
  have hex : ∀ k, ∃ c : ι k, ∀ i, O.valuation (y ⟨k, i⟩) ≤ O.valuation (y ⟨k, c⟩) := fun k => by
    obtain ⟨i, -⟩ := hy k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => O.valuation (y ⟨k, i⟩)) ⟨i, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hex
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hy k
    have := hc k i
    rw [h0, map_zero] at this
    exact hi ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hO : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ O := fun k i => by
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (hc0 k)))]
    exact hc k i
  let w : (Σ k, ι k) → O := fun p => ⟨ratioPt y c p, hO p.1 p.2⟩
  let φ : MRing ι →+* O := eval₂Hom (Int.castRingHom O) w
  have hφ : ∀ s, (φ s : Ω) = aeval (ratioPt y c) s := fun s => by
    have : O.subtype.comp φ = (aeval (ratioPt y c) : MRing ι →ₐ[ℤ] Ω) :=
      ringHom_ext (fun r => by simp) fun p => by simp [φ, w]
    exact DFunLike.congr_fun this s
  have hP : ∀ s ∈ mCoordIdeal y, φ s = 0 := fun s hs => Subtype.ext <| by
    rw [hφ]
    exact aeval_eq_zero_of_mem (mCoordIdeal_ratioPt y c hc0 ▸ hs)
  obtain ⟨u, v, hu, hv, huv⟩ := hU ((IsLocalRing.maximalIdeal O).comap φ) (Ideal.comap_isPrime _ _)
    (fun s hs => by rw [Ideal.mem_comap, hP s hs]; exact zero_mem _) fun k => ⟨c k, fun h => by
      have e : φ (X ⟨k, c k⟩) = 1 := Subtype.ext (by rw [hφ]; simp [ratioPt, hc0])
      rw [Ideal.mem_comap, e] at h
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  have h1 : ∀ s, s ∉ (IsLocalRing.maximalIdeal O).comap φ → O.valuation (φ s) = 1 := fun s hs =>
    (O.valuation_eq_one_iff _).1 (IsLocalRing.notMem_maximalIdeal.1 hs)
  have h2 : O.valuation (aeval (ratioPt y c) f) = O.valuation (aeval (ratioPt y c) g) := by
    have e := congrArg (fun t : O => (t : Ω)) (hP _ huv)
    simp only [map_sub, map_mul] at e
    push_cast at e
    have e' := congrArg O.valuation (sub_eq_zero.1 e)
    rwa [map_mul, map_mul, h1 u hu, h1 v hv, one_mul, one_mul, hφ, hφ] at e'
  have h3 : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (ratioPt y c) s := fun hs => by
    rw [← HilbertSamuel.LiftBirationalNef.aeval_scale (fun k => y ⟨k, c k⟩) hs]
    congr 2
    funext p
    rw [ratioPt, mul_div_cancel₀ _ (hc0 _)]
  have h4 : O.valuation (aeval (ratioPt y c) g) ≠ 0 := by
    rw [map_ne_zero]
    exact right_ne_zero_of_mul (h3 hg ▸ hne hg hgP)
  rw [UnitZ.vdeg_chart O y c hc0 hO, UnitZ.vdeg_chart O y c hc0 hO, h3 hf, h3 hg, map_div₀, map_mul, map_mul, h2,
    mul_div_mul_right _ _ h4, ← map_div₀, ← map_mul, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hc0 k), ← zpow_add₀ (hc0 k), hd, sub_add_cancel]

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_ratio (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (φ : L →+* Ω) (z : (Σ k, ι k) → L), (∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) ∧
      (∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) ∧ Birational z ∧ mCoordIdeal z = mCoordIdeal y := by
  refine ⟨ratioField y c, inferInstance, inferInstance, algebraMap (ratioField y c) Ω, ratioPtL y c, fun _ => rfl, fun t => ?_,
    birational y c hc, mCoordIdeal_ratioPtL y c hc⟩
  rw [← ratioField_eq_blockFnField y c hc]
  exact ⟨fun h => ⟨⟨t, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩

variable {L : Type} [Field L] [CharZero L]

theorem finrank_ratio {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {φ : L →+* Ω} {z : (Σ k, ι k) → L}
    (hφ : ∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) (hr : ∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) :
    Module.finrank (fnField ℚ (z ∘ v)) L = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) := by
  have h1 : (fnField ℚ (z ∘ v)).map φ.toRatAlgHom = blockFnField (y ∘ v) := by
    rw [fnField, IntermediateField.adjoin_map, blockFnField]
    congr 1
    have e : ∀ p q : Σ k, ι₁ k, p.1 = q.1 → φ.toRatAlgHom ((z ∘ v) p / (z ∘ v) q) = (y ∘ v) p / (y ∘ v) q := fun p q h => by
      have h' : (⟨(v p).1, c (v p).1⟩ : Σ k, ι k) = ⟨(v q).1, c (v q).1⟩ :=
        congrArg (fun k => (⟨k, c k⟩ : Σ k, ι k)) ((hv.2.2.1 p).trans ((congrArg κ h).trans (hv.2.2.1 q).symm))
      show φ (z (v p) / z (v q)) = y (v p) / y (v q)
      rw [map_div₀, hφ, hφ, h', div_div_div_cancel_right₀ (hc _)]
    ext t
    constructor
    · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
      exact ⟨p, q, h, e p q h⟩
    · rintro ⟨p, q, h, rfl⟩
      exact ⟨_, ⟨p, q, h, rfl⟩, e p q h⟩
  have h2 : (⊤ : IntermediateField ℚ L).map φ.toRatAlgHom = blockFnField y := by
    ext t
    rw [hr, IntermediateField.mem_map]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  rw [← h1, ← h2, IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right]

open Classical in
theorem num_pull (hP : NumPull) {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hI : mCoordIdeal z = mCoordIdeal y) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) {d : ℕ} (hz : IsPt ℚ z d) {e : ℕ}
    (hf : Module.finrank (fnField ℚ (z ∘ v)) L = e) (he : e ≠ 0) (a : Fin d → K₁ → ℤ) :
    num ℚ z (fun j => pullDeg κ (a j)) =
      (e : ℤ) * NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v)).map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
  have hzv : IsPt ℚ (z ∘ v) d := by
    refine ⟨fun b => ?_, Module.finite_of_finrank_pos (by rw [hf]; exact Nat.pos_of_ne_zero he), hz.2.2⟩
    obtain ⟨i, hi⟩ := hz.1 (κ b)
    obtain ⟨⟨b', j⟩, hp⟩ := hv.2.2.2 ⟨κ b, i⟩ ⟨b, rfl⟩
    obtain rfl : b' = b := hv.1 ((hv.2.2.1 ⟨b', j⟩).symm.trans (congrArg Sigma.fst hp))
    exact ⟨j, by rwa [Function.comp_apply, hp]⟩
  have hI' : mCoordIdeal (z ∘ v) = mCoordIdeal (y ∘ v) := by
    rw [← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, ← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, hI]
  rw [hP ℚ _ _ _ _ _ κ v _ d a hv hz hzv, num, hf, inum, pointIdeal_rat, hI']

theorem isPt_of_birational {z : (Σ k, ι k) → L} (hb : Birational z) {d : ℕ} (hz : IsArithVar (mCoordIdeal z) (d + 1)) :
    IsPt ℚ z d := by
  have h0 : 0 < Module.finrank (RingHom.id L).fieldRange L := by
    rw [show (RingHom.id L).fieldRange = ⊤ from RingHom.fieldRange_eq_top_iff.2 Function.surjective_id]
    have : Module.Finite (⊤ : Subfield L) L :=
      Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield L) L) fun x => ⟨⟨x, trivial⟩, rfl⟩
    exact Module.finrank_pos
  exact (numMap L L (RingHom.id L) K ι z d hb hz h0).1


open Classical in
theorem intNum_cmp (hP : NumPull) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] (y : (Σ k, ι k) → Ω)
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k} (h₁ : IsBlockMap κ₁ v₁)
    (h₂ : IsBlockMap κ₂ v₂) {d : ℕ} (hy : IsArithVar (mCoordIdeal y) (d + 1))
    (e₁ : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    (e₂ : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0) (a₁ : Fin d → K₁ → ℤ) (a₂ : Fin d → K₂ → ℤ)
    (h : ∀ j, ∃ f g, IsLineIso (mCoordIdeal y) (pullDeg κ₁ (a₁ j)) (pullDeg κ₂ (a₂ j)) f g) :
    (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₁)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₁ =
      (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₂)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₂ := by
  choose c hc using ne_of_arith hy
  obtain ⟨L, _, _, φ, z, hφ, hr, hb, hI⟩ := exists_ratio y c hc
  rw [← hI] at hy h
  have hz : IsPt ℚ z d := isPt_of_birational hb hy
  refine (num_pull hP hI h₁ hz (finrank_ratio hc hφ hr h₁) e₁ a₁).symm.trans
    (Eq.trans ?_ (num_pull hP hI h₂ hz (finrank_ratio hc hφ hr h₂) e₂ a₂))
  refine numEq ptDim hP (unitZero ptDim) ℚ L K ι K ι z z d _ _ hz hz fun j => ?_
  obtain ⟨f, g, hfg⟩ := h j
  exact valEq_of_lineIso hz.1 hfg


open Classical MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M in
theorem degNum_eq (hI : PB.Inputs) {d : ℕ} {σ : Type} {S : PB.AnSys d σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (w : Fin d → σ) :
    (Re.deg : ℝ) * S.degNum w =
      (NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => (Re.ref (w j)).a : ℤ) := by
  have href : mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := by
    have hth : ∀ a, IsPotential S.A (S.th a) := fun a => (S.sing a).1
    have hpb : ∀ a, IsPotential Re.R.A ((S.th a).pullback Re.π Re.holo.1) := fun a =>
      isPotentialPullback S.A Re.R.A Re.π Re.holo (S.th a) (hth a)
    have hC2 (a : σ) (x : Re.R.X) : PB.IsTwiceDifferentiableAt Re.R.A ((S.th a).pullback Re.π Re.holo.1) x := by
      intro j hj
      let P' := (S.th a).pullback Re.π Re.holo.1
      let chart := Re.R.A.chart j
      have hx : chart x ∈ chart.target ∩ chart.symm ⁻¹' P'.U x :=
        ⟨chart.map_source hj, by
          rw [Set.mem_preimage, chart.left_inv hj]
          exact P'.mem_U x⟩
      exact (contDiffAt_of_isPotential Re.R.A P' (hpb a) x j hx).of_le (by simp)
    rw [(GlobalTheory.T.monge_ampere_integral_congr_potentials d Re.R.X Re.R.A Set.univ
      (fun j => potOf Re.R (Re.ref (w j))) (fun j => (S.th (w j)).pullback Re.π Re.holo.1)
      (fun _ => 1) (fun _ => 1) (fun j => by simp) (fun j => Re.ref_pot (w j))
      (fun j x _ => hC2 (w j) x) (fun _ _ => rfl)).1]
    let Φ : Fin d → LocPot S.X := fun j => S.th (w j)
    let Ψ : Fin d → LocPot Re.R.X := fun j => (Φ j).pullback Re.π Re.holo.1
    change mInt Re.R.A Ψ (fun _ => 1) = Re.deg * mInt S.A Φ (fun _ => 1)
    rcases isEmpty_or_nonempty S.X with hX | hX
    · have hY : IsEmpty Re.R.X := ⟨fun y => hX.false (Re.π y)⟩
      have hA : ∀ k, (S.A.chart k).target = ∅ := fun k => by
        rw [← (S.A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (S.A.chart k).source, Set.image_empty]
      have hB : ∀ k, (Re.R.A.chart k).target = ∅ := fun k => by
        rw [← (Re.R.A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (Re.R.A.chart k).source, Set.image_empty]
      simp [mInt, integralWith, hA, hB]
    · let : MeasurableSpace S.X := borel S.X
      have : BorelSpace S.X := ⟨rfl⟩
      let : MeasurableSpace Re.R.X := borel Re.R.X
      have : BorelSpace Re.R.X := ⟨rfl⟩
      obtain ⟨A⟩ := existsPartition S.A
      obtain ⟨B⟩ := existsPartition Re.R.A
      obtain ⟨E, V, k, W, j, hEm, hEd, hEU, hEV, hsh⟩ := exists_sheet_partition Re.holo Re.degree
      have hΦ := mIntegrableCont S.A Φ (fun j => hth (w j)) (fun _ => 1) continuous_const
      have hΨ := mIntegrableCont Re.R.A Ψ (fun j => hpb (w j)) (fun _ => 1) continuous_const
      have hXsum := dI_hasSum S.A A Φ (fun _ => 1) (integrableOn_weight S.A A Φ _ hΦ) E hEm hEd Re.br
        (analyticNull S.A Re.br Re.degree.1 Re.degree.2.1) hEU
      have hYsum := dI_hasSum Re.R.A B Ψ (fun _ => 1) (integrableOn_weight Re.R.A B Ψ _ hΨ)
        (fun m => Re.π ⁻¹' E m) (fun m => Re.holo.1.measurable (hEm m))
        (fun m n hmn => (hEd hmn).preimage Re.π) (Re.π ⁻¹' Re.br)
        (analyticNull Re.R.A _ Re.degree.2.2.1 Re.degree.2.2.2.1)
        (by rw [← Set.preimage_iUnion, hEU, Set.preimage_compl])
      have hp (m : ℕ) : integralWith Re.R.A B Ψ ((Re.π ⁻¹' E m).indicator (fun _ => 1)) =
          Re.deg * integralWith S.A A Φ ((E m).indicator (fun _ => 1)) := by
        rw [show (Re.π ⁻¹' E m).indicator (fun _ => (1 : ℝ)) = fun y => (E m).indicator (fun _ => 1) (Re.π y) from
          funext fun y => Set.indicator_comp_right Re.π (s := E m) (g := fun _ => (1 : ℝ)) (x := y)]
        obtain ⟨hV, hVk, hW, hdis, hpre, hbij⟩ := hsh m
        exact (degree_piece Re.holo Φ (fun j => hth (w j)) A B (hEm m) (hEV m) hV hVk hW hdis hpre hbij _ hΦ).2
      simp only [hp] at hYsum
      rw [mIntEq Re.R.A B Ψ (fun j => hpb (w j)) _ hΨ, mIntEq S.A A Φ (fun j => hth (w j)) _ hΦ]
      exact HasSum.unique hYsum (hXsum.mul_left _)
  rw [← href, ← ptsIntegral_one_eq_mInt hI.resExists resBridge Re.R Re.arith fun j => Re.ref_smooth _]
  exact Giv.degreeGeneric_of_degree hI.degree K ι P d _ Re.arith fun j => Re.ref_smooth _

end RootFieldNumerics.Sq
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.PolySmulOfSameSing

section

@[expose] public section

noncomputable section

namespace SquareStatements

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp RootFieldNumerics.Sq
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem cmp_arith {a b e₁ e₂ d₁ d₂ m : ℝ} (p₁ : e₁ ≠ 0) (p₂ : e₂ ≠ 0) (hm : m ≠ 0) (h : e₁ * (m * d₁) = e₂ * d₂) :
    (a / d₁ - (e₁ * a - e₂ * b) / (e₁ * d₁)) / m = b / d₂ := by
  rw [sub_div (e₁ * a), mul_div_mul_left _ _ p₁, sub_sub_cancel, div_div, show e₁ * d₁ * m = e₂ * d₂ by rw [← h]; ring,
    mul_div_mul_left _ _ p₂]

theorem poly_smul_of_sameSing (hN : SheetDecomposition.NumPull) (hIn : PB.Inputs) (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k}
    {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {σ : Type} [Fintype σ] {S₁ S₂ : PB.AnSys D σ}
    {P₁ : Ideal (MRing ι₁)} {P₂ : Ideal (MRing ι₂)} (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) {β : MRing ι} {b : K → ℕ}
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a)
    (hne : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (hdeg : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * (m * Re₁.deg) =
      IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) * Re₂.deg) :
    Re₁.PB II = (m : ℝ) • Re₂.PB II ∧ S₁.degPoly = (m : ℝ) • S₂.degPoly := by
  have hne' : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0 :=
    left_ne_zero_of_mul (hdeg ▸ mul_ne_zero hne (mul_ne_zero hm Re₁.deg_pos.ne'))
  have hW := PairTop.cmpSt_of_eq hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ P₁ P₂ Re₁ Re₂ h₁ h₂ β b hv₁ hv₂ hy hβ hβy
    hA₁ hA₂ hS
  have hG := fun w : Fin D → σ => intNum_cmp hN y hv₁ hv₂ hy hne hne' (fun j => (Re₁.ref (w j)).a) (fun j => (Re₂.ref (w j)).a)
    fun j => (hS (w j)).imp fun f => Exists.imp fun g h => h.1
  rw [h₁, h₂] at hG
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = e₁ at *
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = e₂ at *
  have hdeg' : (e₁ : ℝ) * (m * Re₁.deg) = e₂ * Re₂.deg := by exact_mod_cast hdeg
  have p₁ : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have p₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  have q₁ : (Re₁.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re₁.deg_pos.ne'
  have pm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  constructor
  · rw [PB.Realis.PB, PB.Realis.PB, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly (D + 1)) (funext fun w => ?_)
    obtain ⟨C₃, s₀, -, h⟩ := GlobalTheory.T.agreement_positive hIn D σ S₁ 0 (S₁.reg (w 0)).1
    have c₁ := (h II hII _ _ _ Re₁).1 w
    have c₂ : Tendsto (fun t => Re₂.num II t w) (𝓝[>] 0) (𝓝 (Re₁.limNum II w / m)) := by
      have := (c₁.sub ((hW w).div_const ((e₁ : ℝ) * Re₁.deg))).div_const (m : ℝ)
      rw [zero_div, sub_zero] at this
      refine this.congr fun t => ?_
      exact cmp_arith p₁ p₂ pm hdeg'
    rw [show Re₂.limNum II w = _ from c₂.limUnder_eq, mul_div_cancel₀ _ pm]
  · rw [PB.AnSys.degPoly, PB.AnSys.degPoly, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly D) (funext fun w => ?_)
    have h := congrArg (Int.cast : ℤ → ℝ) (hG w)
    push_cast at h
    rw [← degNum_eq hIn Re₁, ← degNum_eq hIn Re₂, ← mul_assoc, ← mul_assoc, ← hdeg'] at h
    exact mul_left_cancel₀ (mul_ne_zero p₁ q₁) (h.trans (by ring))

theorem stCmp : StCmp := by
  intro hIn hC II hII E _ _ _ H D l Xo c O _ β Y S n M M' T T' hβ hgen hR hd hd'
  classical
  have hm : T.Fl.deg ≠ 0 := by
    obtain ⟨_, _, -, -, -, -, -, -, -, -, h, -⟩ := T.Fl.generic
    exact h.ne'
  have hsab : SABMap (twistSAB Xo.univ.t (HostAut.refl H)) Xo.univ.t (Iso.refl Xo.X).hom := by
    rw [(twistSAB_symm_refl E H Xo.X Xo.univ.t (HostAut.refl H)).2.2]
    exact (exists_sabMap_id E H Xo.X Xo.univ.t).choose
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt GlobalTheory.T.theta_uniformisation_complex_abelian_varieties E H D l Xo c O β Y (HostAut.refl H) (Iso.refl Xo.X) hsab (Equiv.refl _) S n M M' T T'
      hβ (by simp) (fun τ => by ext; rfl)
      (Indep.imageCpt_refl_of_genPt E H D l Xo c O β Y S _ _ _ _ _ _ _ _ T.A T'.A hβ hgen) hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  choose Lr hLr using fun r => (hJ.1 (T.sing r)).exists
  choose Lr' hLr' using fun r => (hJ'.1 (T'.sing r)).exists
  refine poly_smul_of_sameSing SheetDecomposition.numPull hIn hC II hII T.Re T'.Re hP hP' hbv hbv' harith hmh hb T.alg T'.alg (fun a => ?_) hne hm
    (by rw [hd, hd', mul_one, hdeg])
  exact GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy T'.Sy T.Re T'.Re b a a _ _ _ _ hbv hbv'
    (hc4 _ _ κ v _ _ _ _ hbv hLr) (hc4 _ _ κ' v' _ _ _ _ hbv' hLr') (T.ref_deg a) (T'.ref_deg a) (T.sing_eq a)
    (T'.sing_eq a) hmpp (hc1 _ Lr Lr' _ fun r => hiso r _ _ (hLr r) (hLr' r))

end SquareStatements
end
end
end
