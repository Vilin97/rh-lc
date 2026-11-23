module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.FiniteDimensionalFromLinearForms
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.IntegrableMulBc
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogBallEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogNormEstimates
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpotentSubgroupRepresentation
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.PBAdel
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.RealParabolicDecomposition
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.RowsFinDimOf
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.SecondOrderExpAtInfinitePlace

-- Source module: CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.CuspidalAtInfinityOf

section

@[expose] public section

open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem cuspidal_at_infinity_of : Sel → Avg → NWSub → RealPar → ParPi → Transp → GamSub → GeoInf → CuspInf := by
  classical
  intro hSel hAvg hNW hRP hPi hT hGam hGeo I M hM ph hph hconv U hU
  obtain ⟨K, hKn, hKU, hK⟩ := local_compact_nhds hU
  obtain ⟨C, hC, hy⟩ := hGeo I M hM (interior K) (interior_mem_nhds.2 hKn)
  refine ⟨C, hC, fun y => (hy y).imp_right ?_⟩
  rintro ⟨W, hW0, hWi, hcov⟩
  obtain ⟨-, -, -, hperp, hne, -⟩ := hT I
  have hiso : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    unfold Isot
    rw [← hperp]
    exact Submodule.span_mono (image_mono hWi)
  choose Nv hNv using fun v => (hNW _ _ _ (hiso v)).2
  let N : Subgroup I.Ginf := Subgroup.pi univ Nv
  have hNm : ∀ g, g ∈ N ↔ g ∈ NInf I W := fun g => by
    simp only [N, Subgroup.mem_pi, mem_univ, forall_true_left, NInf, mem_ofPred_eq, ← hNv, SetLike.mem_coe]
  have hNc : IsClosed (N : Set I.Ginf) := by
    rw [Subgroup.coe_pi]
    exact isClosed_set_pi fun v _ => by rw [hNv]; exact (hNW _ _ _ (hiso v)).1
  obtain ⟨Γ, hΓ, hΓd⟩ := hGam I M
  have hc : Continuous fun m : I.Ginf => y⁻¹ * m * y := by fun_prop
  have hcK : IsCompact ((fun m : I.Ginf => y⁻¹ * m * y) ⁻¹' K) :=
    (((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage).2 hK
  obtain ⟨ν, hν, hνV, hinv⟩ := hAvg I.Ginf N (Γ ⊓ N) hNc inf_le_right
    (fun B hB => (hΓd B hB).subset fun x hx => ⟨hx.1, hx.2.1⟩) ((fun m => y⁻¹ * m * y) ⁻¹' interior K)
    (isOpen_interior.preimage hc)
    (hcK.of_isClosed_subset isClosed_closure (closure_minimal (preimage_mono interior_subset) hcK.isClosed))
    fun m hm => by
      obtain ⟨γ, hγ, hγN, h⟩ := hcov m ((hNm m).1 hm)
      exact ⟨γ, ⟨hΓ.ge hγ, (hNm γ).2 hγN⟩, h⟩
  refine ⟨ν, hν, hνV.mono fun m hm => hKU (interior_subset hm), fun u hu huΓ hrep x => ?_⟩
  obtain ⟨huc, B, hB⟩ := id hu
  have hc2 : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * p.2) := huc.comp continuous_mul
  let F : I.Ginf → ℂ := fun x => ∫ m, u (m * x) ∂ν
  have hFb : BC F := ⟨continuous_of_dominated (bound := fun _ => B)
      (fun x => (hc2.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun _ => hB _) (integrable_const _)
      (Eventually.of_forall fun m => hc2.comp (continuous_const.prodMk continuous_id)),
    B, fun x => by simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun m => hB (m * x))⟩
  have hFN : LInv N F := fun m hm x => hinv u hu (fun γ hγ => huΓ γ (by rw [← hΓ]; exact hγ.1)) m hm x
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  obtain ⟨a, Ht, P⟩ := hRP _ _ _ (hne v₀ W hW0) (hiso v₀) (Nv v₀) (hNv v₀)
  have h0 := hSel I.Ginf (muInf I) ph hph hconv _ _ _ (hPi _ _ v₀ _ a Ht P) F hFb (by
    rintro _ ⟨m, hm, rfl⟩
    refine hFN _ fun v _ => ?_
    by_cases hv : v = v₀
    · subst hv; simpa using hm
    · simp [Pi.mulSingle_eq_of_ne hv]) x
  have hI : Integrable (fun p : I.Ginf × I.Ginf => ph p.2 * u (p.1 * x * p.2)) (ν.prod (muInf I)) :=
    (hph.comp_snd ν).mul_bdd
      (huc.comp (by fun_prop) : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * x * p.2)).aestronglyMeasurable
      (Eventually.of_forall fun _ => hB _)
  rw [← h0, integral_congr_ae (Eventually.of_forall fun m => hrep (m * x)), integral_integral_swap hI]
  simp only [F, integral_const_mul, mul_assoc]

theorem level_structure_of : LevelOf := by
  intro I e hlc hs
  let K : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
  have hK : IsCompact (K : Set I.Gf) := PI.WAU.maximal_compact_isCompact I
  have hKo : IsOpen (K : Set I.Gf) := Formalism.L2.SG.Pf.kset_open I
  let Kp : Subgroup I.Gf :=
    { carrier := {k | k ∈ K ∧ ∀ x, e (k * x) = e x}
      mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, fun x => by rw [mul_assoc, ha.2, hb.2]⟩
      one_mem' := ⟨K.one_mem, fun x => by rw [one_mul]⟩
      inv_mem' := fun {k} hk => ⟨K.inv_mem hk.1, fun x => by rw [← hk.2 (k⁻¹ * x), mul_inv_cancel_left]⟩ }
  have h1 : ∀ᶠ k in 𝓝 (1 : I.Gf), ∀ x ∈ (K : Set I.Gf), e (k * x) = e x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have a1 := (hlc.comp_continuous (continuous_mul (M := I.Gf))).eventually_eq (1, x)
    have a2 := (hlc.comp_continuous (continuous_snd (X := I.Gf))).eventually_eq (1, x)
    filter_upwards [a1, a2] with p h1 h2
    simp only [Function.comp_apply, one_mul] at h1 h2
    rw [h1, h2]
  have hop : IsOpen (Kp : Set I.Gf) := by
    refine Kp.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [h1, hKo.mem_nhds K.one_mem] with k hk hkK
    refine ⟨hkK, fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact hk x hx
    · have a1 : e x = 0 := by by_contra h; exact hx (hs x h)
      have a2 : e (k * x) = 0 := by by_contra h; exact hx ((K.mul_mem_cancel_left hkK).1 (hs _ h))
      rw [a1, a2]
  exact ⟨Kp, hop, hK.of_isClosed_subset (Kp.isClosed_of_isOpen hop) fun k hk => hk.1, fun k hk => hk.2⟩

end CompanionTheory.D.gk.RF
end
end
end

-- Source module: CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ParabolicSubgroupDecomposition

section

@[expose] public section

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

theorem Disc.countable {G : Type} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {Λ : Subgroup G} (h : Disc Λ) : Countable Λ := by
  have : (Λ : Set G).Countable := by
    have e : (Λ : Set G) = ⋃ n, compactCovering G n ∩ Λ := by rw [← iUnion_inter, iUnion_compactCovering, univ_inter]
    rw [e]
    exact countable_iUnion fun n => (h _ (isCompact_compactCovering G n)).countable
  exact this.to_subtype

theorem Disc.exists_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] {Λ : Subgroup G} (h : Disc Λ) :
    ∃ O ∈ 𝓝 (1 : G), ∀ a ∈ O, ∀ b ∈ O, a * b⁻¹ ∈ Λ → a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hcl : IsClosed ((K ∩ Λ) \ {1}) := ((h K hK).subset sdiff_subset).isClosed
  have hW : K ∩ ((K ∩ Λ) \ {1})ᶜ ∈ 𝓝 (1 : G) := inter_mem hK1 (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
  obtain ⟨O, hO, hOW⟩ := exists_nhds_split_inv hW
  refine ⟨O, hO, fun a ha b hb hab => ?_⟩
  have := hOW a ha b hb
  rw [div_eq_mul_inv] at this
  by_contra hne
  exact this.2 ⟨⟨this.1, hab⟩, fun e => hne (mul_inv_eq_one.1 e)⟩

theorem fundamental_domain_inclusion : FundIn := by
  classical
  intro N _ _ _ _ _ _ _ _ Λ hd V hV hcov
  obtain ⟨O, hO, hinj⟩ := hd.exists_nhds
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun p : N => interior ((fun x => x * p⁻¹) ⁻¹' O)) fun p =>
      interior_mem_nhds.2 ((continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hO))
  have hTne : T.Nonempty := by
    have : (1 : N) ∈ ⋃ x ∈ T, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨p, hp, -⟩ := mem_iUnion₂.1 this
    exact ⟨p, hp⟩
  obtain ⟨p, rfl⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set N := fun i => V ∩ interior ((fun x => x * (p i)⁻¹) ⁻¹' O)
  have hWo : ∀ i, IsOpen (W i) := fun i => hV.inter isOpen_interior
  let S : ℕ → Set N := fun i => {m | ∃ l ∈ Λ, l * m ∈ W i}
  have hSo : ∀ i, IsOpen (S i) := fun i => by
    have : S i = ⋃ l ∈ Λ, (fun m => l * m) ⁻¹' W i := by ext m; simp [S]
    rw [this]
    exact isOpen_biUnion fun l _ => (hWo i).preimage (continuous_const.mul continuous_id)
  have hSi : ∀ i, ∀ l ∈ Λ, ∀ m, l * m ∈ S i ↔ m ∈ S i := fun i l hl m =>
    ⟨fun ⟨l', hl', h⟩ => ⟨l' * l, Λ.mul_mem hl' hl, by rwa [mul_assoc]⟩,
      fun ⟨l', hl', h⟩ => ⟨l' * l⁻¹, Λ.mul_mem hl' (Λ.inv_mem hl), by simpa [mul_assoc] using h⟩⟩
  have hex : ∀ m, ∃ i, m ∈ S i := fun m => by
    obtain ⟨l, hl, hlm⟩ := hcov m
    have : l * m ∈ ⋃ x ∈ range p, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_iUnion₂.1 this
    exact ⟨i, l, hl, hlm, hi⟩
  refine ⟨⋃ i, W i \ ⋃ j < i, S j, MeasurableSet.iUnion fun i => (hWo i).measurableSet.diff
    (isOpen_biUnion (s := {j : ℕ | j < i}) fun j _ => hSo j).measurableSet,
    iUnion_subset fun i => sdiff_subset.trans inter_subset_left,
    fun m => ?_⟩
  have key : ∀ l : Λ, ∀ i, (l : N) * m ∈ W i \ ⋃ j < i, S j → i = Nat.find (hex m) := fun l i h => by
    refine ((Nat.find_eq_iff (hex m)).2 ⟨⟨l, l.2, h.1⟩, fun j hj hm => h.2 ?_⟩).symm
    exact mem_iUnion₂.2 ⟨j, hj, (hSi j l l.2 m).2 hm⟩
  obtain ⟨l, hl, hlm⟩ := Nat.find_spec (hex m)
  refine ⟨⟨l, hl⟩, mem_iUnion.2 ⟨_, hlm, fun h => ?_⟩, fun l' hl' => ?_⟩
  · obtain ⟨j, hj, hm⟩ := mem_iUnion₂.1 h
    exact Nat.find_min (hex m) hj ((hSi j l hl m).1 hm)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hl'
    obtain rfl := key l' i hi
    have a1 := mem_preimage.1 (interior_subset hi.1.2)
    have a2 := mem_preimage.1 (interior_subset hlm.2)
    have := hinj _ a1 _ a2 (by
      simpa [mul_assoc] using Λ.mul_mem l'.2 (Λ.inv_mem hl))
    exact Subtype.ext (mul_right_cancel (mul_right_cancel this))

theorem averaging_of_fundamental_domain : FundIn → Avg := by
  intro hF G _ _ _ _ _ _ _ _ N Λ hN hle hd V hV hVc hcov
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  let Λ' : Subgroup N := Λ.subgroupOf N
  have hd' : Disc Λ' := fun C hC =>
    ((hd _ (hC.image continuous_subtype_val)).preimage Subtype.val_injective.injOn).subset
      fun x hx => ⟨mem_image_of_mem _ hx.1, hx.2⟩
  have := hd'.countable
  obtain ⟨D, hDm, hDV, hD⟩ := hF N Λ' hd' (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) fun m => by
    obtain ⟨l, hl, h⟩ := hcov m m.2
    exact ⟨⟨l, hle hl⟩, hl, h⟩
  let μ : Measure N := Measure.haar
  have hFD : ∀ g : N, IsFundamentalDomain Λ' ((fun x => x * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' (measurable_mul_const g hDm).nullMeasurableSet fun m => by
      simpa [Subgroup.smul_def, mul_assoc] using hD (m * g)
  have hFD1 : IsFundamentalDomain Λ' D μ := by simpa using hFD 1
  have hfin : μ D ≠ ∞ := ((measure_mono (hDV.trans (preimage_mono subset_closure))).trans_lt
    (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hVc).measure_lt_top).ne
  have hpos : μ D ≠ 0 := hFD1.measure_ne_zero (NeZero.ne μ)
  have hR : ∀ g : N, μ.map (fun x => x * g) = μ := fun g => by
    have h1 := Measure.isMulLeftInvariant_eq_smul (μ.map fun x => x * g) μ
    have h2 := congrArg (fun m : Measure N => m D) h1
    simp only [Measure.map_apply (measurable_mul_const g) hDm, Measure.smul_apply] at h2
    rw [(hFD g).measure_eq hFD1, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : ((μ.map fun x => x * g).haarScalarFactor μ : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hpos hfin).1 (h2.symm.trans (one_mul _).symm)
    rw [h1, show (μ.map fun x => x * g).haarScalarFactor μ = 1 by exact_mod_cast h3, one_smul]
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hP : IsProbabilityMeasure ((μ D)⁻¹ • μ.restrict D) :=
    ⟨by rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]⟩
  refine ⟨((μ D)⁻¹ • μ.restrict D).map Subtype.val, (Measure.isProbabilityMeasure_map_iff hE.measurable.aemeasurable).2 hP,
    hE.ae_map_iff.2 (Measure.ae_smul_measure ((ae_restrict_mem hDm).mono fun x hx => hDV hx) _),
    fun u _ hu m₀ hm₀ y => ?_⟩
  rw [hE.integral_map, hE.integral_map, integral_smul_measure, integral_smul_measure]
  congr 1
  let g : N := ⟨m₀, hm₀⟩
  have hmp : MeasurePreserving (fun x : N => x * g⁻¹) μ μ := ⟨measurable_mul_const _, hR _⟩
  rw [← (hFD g⁻¹).setIntegral_eq hFD1 (f := fun m : N => u (m * y)) fun l x => by
      show u (((l : N) : G) * x * y) = _
      rw [mul_assoc]; exact hu _ l.2 _,
    ← hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g⁻¹) (fun m : N => u (m * (m₀ * y))) D]
  congr 1
  funext x
  simp [g]

theorem parabolic_subgroup_decomposition : ParPi := by
  intro ι _ _ G _ _ _ i₀ N a Ht P
  refine ⟨(continuous_mulSingle i₀).comp P.cont, fun s t => by rw [P.add, Pi.mulSingle_mul], ?_,
    P.hcont.comp (continuous_apply i₀), ?_, fun t g => by simp [P.ha], ?_, fun U hU => ?_⟩
  · rintro t _ ⟨m, hm, rfl⟩
    refine ⟨_, P.norm t m hm, ?_⟩
    simp [Pi.mulSingle_mul, Pi.mulSingle_inv]
  · rintro _ ⟨m, hm, rfl⟩ g
    simp [P.hN m hm]
  · obtain ⟨c, hc, hb⟩ := P.bd
    exact ⟨fun y => c (y i₀), hc.comp (continuous_apply i₀), fun x y => hb _ _⟩
  · obtain ⟨τ, hτ, h⟩ := P.small (Pi.mulSingle i₀ ⁻¹' U)
      ((continuous_mulSingle i₀).continuousAt.preimage_mem_nhds (by simpa using hU))
    refine ⟨τ, hτ, fun t ht x => ?_⟩
    obtain ⟨m, hm, hx⟩ := h t ht (x i₀)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    refine (congrArg (· ∈ U) ?_).mpr (mem_preimage.1 hx)
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Pi.mulSingle_eq_of_ne hi]

end CompanionTheory.D.gk.RF
end
end
end

-- Source module: CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional

section

@[expose] public section

namespace CompanionTheory.D.gk.RF

theorem gamSub : GamSub := by
  exact arithmetic_subgroup_of_transport transport_to_standard_form

theorem geoInf : GeoInf := by
  have hT : Transp := transport_to_standard_form
  have hG : GamSub := arithmetic_subgroup_of_transport hT
  exact reduction_geometry_at_infinity successive_minima_gap (short_isotropic_vector_of hT) covolume_span (covolume_orthogonal_complement hT)
    (mahler_compactness_of hT hG) (nilpotent_cover_of hT hG nilpotent_lie_algebra nilpotent_subgroup_representation)

theorem cuspInf : CuspInf :=
  cuspidal_at_infinity_of selP (averaging_of_fundamental_domain fundamental_domain_inclusion) unipotent_radical_subgroup real_parabolic_decomposition parabolic_subgroup_decomposition transport_to_standard_form gamSub geoInf

theorem automorphic_forms_finite_dimensional : Formalism.L2.SG.RowsDef.RowsFinDim := by
  exact rowsFinDim_of discrete_series_bound_of_inputs finite_dimensional_from_linear_forms (adelic_cusp_of_infinite_cusp cuspInf congruence_subgroup_compact_open)
    (fundamental_domain_discrete_of gamSub) level_structure_of convolution_operator_representation representation_of_convolution

end CompanionTheory.D.gk.RF
end
end
