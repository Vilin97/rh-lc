module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePreimageOfNhdsZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlacesStatement
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Filter.Cofinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegralsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolumeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsumRestrictedFamilyEqProdFinsum

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem finsum_restrictedFamily_eq_prod_finsum : ∀ (V W : Type) [Fintype W] (C : V → Type) [∀ v, One (C v)] (X : ∀ v, Set (C v)) (Y : W → Type) [∀ w, Finite (Y w)], (∀ v, (X v).Finite) → ∀ (o : ∀ v, X v → ℂ) (oa : ∀ w, Y w → ℂ), (∀ᶠ v in cofinite, (1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) → (Function.support fun p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1} => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)).Finite ∧ ∑ᶠ p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}, (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = (∏ᶠ v, ∑ᶠ q : X v, o v q) * ∏ w, ∑ᶠ q : Y w, oa w q := by
  intro V W _ C _ X Y _ hX o oa hev
  classical
  have hfin := Filter.eventually_cofinite.1 hev
  set S : Finset V := hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → ((1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) := by
    intro v hv
    by_contra h
    exact hv (by simpa [hSdef] using h)
  haveI : ∀ v, Fintype (X v) := fun v => (hX v).fintype
  haveI : ∀ w, Fintype (Y w) := fun w => Fintype.ofFinite _
  let Sub := {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  let F : Sub → ℂ := fun p => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)
  let emb : (∀ v : S, X v) × (∀ w, Y w) → Sub := fun t =>
    ⟨(fun v => if h : v ∈ S then t.1 ⟨v, h⟩ else ⟨1, (hS v h).1⟩, t.2), by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      simp [dif_neg (show v ∉ S from h)] at hv⟩
  have hmul : ∀ p : Sub, (Function.mulSupport fun v => o v (p.1.1 v)).Finite := by
    intro p
    refine (S.finite_toSet.union (Filter.eventually_cofinite.1 p.2)).subset ?_
    intro v hv
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (((hS v h.1).2 _).1 h.2)
  have hsupp : Function.support F ⊆ Set.range emb := by
    intro p hp
    have h1 : ∀ v, v ∉ S → (p.1.1 v).1 = 1 := by
      intro v hv
      by_contra hne
      apply hp
      show (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = 0
      rw [finprod_eq_zero _ v (((hS v hv).2 _).2 hne) (hmul p), zero_mul]
    refine ⟨(fun v => p.1.1 v, p.1.2), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext v
      by_cases hv : v ∈ S
      · simp only [emb, dif_pos hv]
      · simp only [emb, dif_neg hv]
        exact Subtype.ext (h1 v hv).symm
    · rfl
  have hinj : Function.Injective emb := by
    intro t t' h
    have h' := congrArg (fun p : Sub => p.1) h
    simp only [emb, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    refine Prod.ext (funext fun v => ?_) h2
    have := congrFun h1 v.1
    simpa only [dif_pos v.2] using this
  have hval : ∀ t, F (emb t) = (∏ v : S, o v (t.1 v)) * ∏ w, oa w (t.2 w) := by
    intro t
    show (∏ᶠ v, o v ((emb t).1.1 v)) * ∏ w, oa w (t.2 w) = _
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [emb, dif_pos v.2]
    · intro v hv
      by_contra h
      apply hv
      simp only [emb, dif_neg (show v ∉ S from h)]
      exact ((hS v h).2 _).1 rfl
  have hsupp' : Function.support F ⊆ ↑(Finset.univ.image emb) := by
    intro p hp
    obtain ⟨t, rfl⟩ := hsupp hp
    simp
  refine ⟨(Finset.univ.image emb).finite_toSet.subset hsupp', ?_⟩
  show ∑ᶠ p, F p = _
  rw [finsum_eq_sum_of_support_subset _ hsupp', Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [hval]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum, ← Fintype.prod_sum, ← Fintype.prod_sum]
  congr 1
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [finsum_eq_sum_of_fintype]
    · intro v hv
      by_contra h
      apply hv
      show ∑ᶠ q : X v, o v q = 1
      rw [finsum_eq_single _ ⟨1, (hS v h).1⟩]
      · exact ((hS v h).2 _).1 rfl
      · intro q hq
        exact ((hS v h).2 q).2 (fun e => hq (Subtype.ext e))
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [finsum_eq_sum_of_fintype]

end GlobalTheory.TrEll
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegrals

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt (ratClass classKernel)

theorem classKernel_eq_sum {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (g : H) (f : G → ℂ)
    (x : G) (T : Finset H) (hT : ∀ δ, f (x⁻¹ * ι δ * x) ≠ 0 → δ ∈ T) :
    classKernel ι.range (ι g) f x = ∑ δ ∈ T, {δ | IsConj g δ}.indicator (fun δ => f (x⁻¹ * ι δ * x)) δ := by
  let e : {δ | IsConj g δ} → ratClass ι.range (ι g) := fun δ => ⟨ι δ, by
    obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
    exact ⟨ι c⁻¹, ⟨_, rfl⟩, by rw [← hc]; simp⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c⁻¹ * g * c, isConj_iff.2 ⟨c⁻¹, by simp⟩⟩, Subtype.ext (by simp [e])⟩
  rw [classKernel, ← (Equiv.ofBijective e he).tsum_eq fun δ => f (x⁻¹ * δ * x)]
  refine (tsum_subtype {δ | IsConj g δ} fun δ => f (x⁻¹ * ι δ * x)).trans (tsum_eq_sum fun δ hδ => ?_)
  by_contra h
  exact hδ (hT δ fun h0 => h (by simp [indicator, h0]))

theorem finsum_eq_sum_classKernel {G H I : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι)
    (p : H → Prop) (g : I → H) (hp : ∀ δ, p δ ↔ ∃ i, IsConj (g i) δ) (hg : ∀ i j, IsConj (g i) (g j) → i = j)
    (f : G → ℂ) (S : Finset I) (hS : ∀ i ∉ S, ∀ x, f (x⁻¹ * ι (g i) * x) = 0) (x : G)
    (hx : {δ | f (x⁻¹ * ι δ * x) ≠ 0}.Finite) :
    ∑ᶠ δ : {δ // p δ}, f (x⁻¹ * ι δ.1 * x) = ∑ i ∈ S, classKernel ι.range (ι (g i)) f x := by
  classical
  rw [Finset.sum_congr rfl fun i _ => classKernel_eq_sum ι hι (g i) f x hx.toFinset fun δ h => hx.mem_toFinset.2 h,
    Finset.sum_comm]
  refine (finsum_set_coe_eq_finsum_mem (f := fun δ => f (x⁻¹ * ι δ * x)) {δ | p δ}).trans ?_
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := hx.toFinset) _ fun δ h => by
    simpa using fun h0 => h (by simp [indicator, h0])]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  by_cases h : p δ
  · obtain ⟨i, hi⟩ := (hp δ).1 h
    have hiS : i ∈ S := by
      by_contra hn
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      refine hx.mem_toFinset.1 hδ ?_
      rw [← hS i hn ((ι c)⁻¹ * x), ← hc]
      simp [mul_assoc]
    rw [indicator_of_mem (show δ ∈ {δ | p δ} from h), Finset.sum_eq_single_of_mem i hiS fun j _ hj =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => hj (hg j i (hc.trans hi.symm))) _,
      indicator_of_mem (show δ ∈ {δ | IsConj (g i) δ} from hi)]
  · rw [indicator_of_notMem (show δ ∉ {δ | p δ} from h), Finset.sum_eq_zero fun j _ =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => h ((hp δ).2 ⟨j, hc⟩)) _]

theorem classKernel_eq_zero {G : Type} [Group G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    classKernel Γ γ f = 0 := by
  funext x
  refine (tsum_congr ?_).trans tsum_zero
  rintro ⟨_, c, -, rfl⟩
  rw [← h (c * x)]
  simp [mul_assoc]

theorem finite_of_eventually_eq_one {V Y : Type} [Finite Y] {C : V → Type} [∀ v, One (C v)] [∀ v, Finite (C v)]
    {X : ∀ v, Set (C v)} {p : (∀ v, X v) × Y → Prop} (A : Set {q // p q})
    (h : ∀ᶠ v in cofinite, ∀ i ∈ A, (i.1.1 v).1 = 1) : A.Finite := by
  have : Finite {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} := eventually_cofinite.1 h
  refine Set.Finite.of_finite_image
    (f := fun i : {q // p q} => ((fun v : {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} => i.1.1 v), i.1.2)) (Set.toFinite _)
    fun i hi j hj e => Subtype.ext (Prod.ext (funext fun v => ?_) (congrArg Prod.snd e :))
  by_cases hv : ∀ i ∈ A, (i.1.1 v).1 = 1
  · exact Subtype.ext ((hv i hi).trans (hv j hj).symm)
  · exact congrFun (congrArg Prod.fst e) ⟨v, hv⟩

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem exists_isCompact_tensor (ha : ∀ w, HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    ∃ C, IsCompact C ∧ ∀ y, tensor σ J fa ff y ≠ 0 → y ∈ C := by
  refine ⟨_, (infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod
    ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi ha))
      hf.tensorFin_mem.2), fun y hy => ?_⟩
  rw [tensor_eq_infFin] at hy
  exact ⟨fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hy) w (Finset.mem_univ w)),
    subset_tsupport _ (right_ne_zero_of_mul hy)⟩

theorem ne_zero_of_tensor (hf : IsFinFamily σ J L ff) {y : GAd σ J} (hy : tensor σ J fa ff y ≠ 0) (v) :
    ff v (proj σ J v y) ≠ 0 := by
  rw [tensor_eq_infFin] at hy
  simpa only [projFinLoc_projFin] using (hf.tensorFin_ne_zero_iff _).1 (right_ne_zero_of_mul hy) v


omit [NumberField F] [NumberField E] in
theorem charpoly_eq_of_isConj {γ δ : GRat σ J} (h : IsConj γ δ) : δ.1.1.charpoly = γ.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have : (c * γ * c⁻¹).1.1 = c.1.1 * γ.1.1 * (c.1⁻¹).1 := rfl
  rw [this, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Adelic

theorem integral_polKernel : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  classical
  intro E _ _ F _ σ hCM hun r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  obtain ⟨H1, H2, H3⟩ := GlobalTheory.T.rational_unitary_classes_iff_local_class_families E F σ hCM hun r P J hJ
  obtain ⟨Ff, Fa⟩ := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hCM r P
  have hae := GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hCM r P J hJ L
  have hcl := GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals F E σ hCM r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  let I := {p : (∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) × (∀ w : InfinitePlace F, XSet P w.Completion J) //
    ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  obtain ⟨hsupp, hsum⟩ := finsum_restrictedFamily_eq_prod_finsum (HeightOneSpectrum (𝓞 F)) (InfinitePlace F)
    (fun v => Cls P (Fv F v)) (fun v => XSet P (Fv F v) J) (fun w => XSet P w.Completion J) (fun v => Set.toFinite _)
    (fun v => orbCls (μf v) (dtf v) (ff v)) (fun w => orbCls (μa w) (dta w) (fa w)) (by
      filter_upwards [hae, hff.2, hμ.eventually_eq_one, IsRestrictedProd.eventually_eq_one hdt] with v h1 h2 h3 h4
      rw [h2]
      exact ⟨h1.1, h1.2.2.2 _ _ (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) h3 h4⟩)
  choose g g1 g2 g3 using fun i : I => H3 (fun v => (i.1.1 v).1) (fun w => (i.1.2 w).1) (fun v => (i.1.1 v).2)
    (fun w => (i.1.2 w).2) i.2
  have hp : ∀ δ : GRat σ J, δ.1.1.charpoly = P.1 ↔ ∃ i, IsConj (g i) δ := fun δ => by
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (charpoly_eq_of_isConj hi).trans (g1 i)⟩
    obtain ⟨a1, a2, a3⟩ := H1 δ h
    choose qf qf1 qf2 using a1
    choose qa qa1 qa2 using a2
    let i : I := ⟨(fun v => ⟨qf v, (qf1 v).mem⟩, fun w => ⟨qa w, (qa1 w).mem⟩), a3.mono fun v hv => (qf2 v 1 hv).symm⟩
    refine ⟨i, IsConj.symm ((H2 δ (g i) h (g1 i)).2 ⟨fun v q hq => ?_, fun w q hq => ?_⟩)⟩
    · rw [qf2 v q hq]; exact g2 i v
    · rw [qa2 w q hq]; exact g3 i w
  have hg : ∀ i j, IsConj (g i) (g j) → i = j := fun i j h => by
    obtain ⟨b1, b2⟩ := (H2 _ _ (g1 i) (g1 j)).1 h
    obtain ⟨a1, a2, -⟩ := H1 _ (g1 j)
    have e1 : ∀ v, i.1.1 v = j.1.1 v := fun v => Subtype.ext ((a1 v).unique (b1 v _ (g2 i v)) (g2 j v))
    have e2 : ∀ w, i.1.2 w = j.1.2 w := fun w => Subtype.ext ((a2 w).unique (b2 w _ (g3 i w)) (g3 j w))
    exact Subtype.ext (Prod.ext (funext e1) (funext e2))
  have hfin : {i : I | ∃ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) ≠ 0}.Finite := by
    refine finite_of_eventually_eq_one _ ?_
    filter_upwards [hae, hff.2] with v h1 h2
    rintro i ⟨x, hx⟩
    have h3 := ne_zero_of_tensor hff hx v
    rw [h2, map_mul, map_mul, map_inv] at h3
    exact h1.2.1 _ _ (g2 i v) ⟨_, by_contra fun hn => h3 (indicator_of_notMem hn _)⟩
  have hS : ∀ i ∉ hfin.toFinset, ∀ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) = 0 := fun i hi x =>
    by_contra fun h => hi (hfin.mem_toFinset.2 ⟨x, h⟩)
  obtain ⟨C, hC, hC'⟩ := exists_isCompact_tensor (fun w => (hfa w).2) hff
  have hker0 : ∀ x, polKernel P J (tensor σ J fa ff) x = ∑ i ∈ hfin.toFinset,
      classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff) x := fun x => by
    rw [polKernel, ← range_ratEmb]
    exact finsum_eq_sum_classKernel (ratEmb σ J) (ratEmb_injective σ J) _ g hp hg _ _ hS x
      (((GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hCM r J C hC).2 x).subset fun δ h => hC' _ h)
  have hker : descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) = fun q => ∑ i ∈ hfin.toFinset,
      descend (ratPts σ J) (classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff)) q := by
    funext q
    simp only [descend, hker0]
  have hi := fun i : I => hcl (g i) (g1 i) i.1.1 i.1.2 (g2 i) (g3 i)
  rw [hker]
  refine ⟨integrable_finsetSum _ fun i _ => (hi i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hi i).1, Finset.sum_congr rfl fun i _ => (hi i).2, mul_assoc]
  simp only [Phi]
  rw [← hsum, mul_finsum' _ _ hsupp]
  refine (finsum_eq_sum_of_support_subset _ fun i hn => ?_).symm
  by_contra h
  refine hn ((hi i).2.symm.trans ?_)
  rw [classKernel_eq_zero _ _ _ (hS i h)]
  simp only [descend, Pi.zero_apply, integral_zero]

end GlobalTheory.TrEll
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegralsStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  first | exact @GlobalTheory.TrEll.integral_polKernel | exact GlobalTheory.TrEll.integral_polKernel | (intros; apply GlobalTheory.TrEll.integral_polKernel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllSum


open Classical in
theorem finsum_subtype_ite {G : Type} (p : G → Prop) {u : G → ℂ} (hu : (Function.support u).Finite) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ δ ∈ hu.toFinset, if p δ then u δ else 0 := by
  rw [finsum_subtype_eq_finsum_cond (f := u) (p := p), finsum_eq_sum_of_support_subset (s := hu.toFinset)]
  · exact Finset.sum_congr rfl fun δ _ => finsum_eq_if
  · intro δ hδ
    simp only [Finite.coe_toFinset]
    intro h0
    exact hδ (by simp [h0])

theorem finsum_group {G Q I : Type} (c : G → Q) (ι : I → Q) (hι : Function.Injective ι) (p : G → Prop)
    (hp : ∀ g, p g ↔ ∃ i, c g = ι i) {u : G → ℂ} (hu : (Function.support u).Finite) (S : Finset I)
    (hS : ∀ g i, u g ≠ 0 → c g = ι i → i ∈ S) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ i ∈ S, ∑ᶠ δ : {δ // c δ = ι i}, u δ.1 := by
  classical
  rw [finsum_subtype_ite p hu, Finset.sum_congr rfl fun i _ => finsum_subtype_ite (fun δ => c δ = ι i) hu,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : u g ≠ 0 := by simpa using hg
  by_cases h : p g
  · obtain ⟨i, hi⟩ := (hp g).1 h
    rw [ite_eq_left h, Finset.sum_eq_single_of_mem i (hS g i hg' hi) fun j _ hj =>
      ite_eq_right fun e => hj (hι (e.symm.trans hi)), ite_eq_left hi]
  · rw [ite_eq_right h]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun e => h ((hp g).2 ⟨i, e⟩)).symm

theorem elliptic_expansion {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {r : ℕ} {J : Matrix (Fin r) (Fin r) E}
    (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff)
    (dta : ∀ (P : PPol σ r) (w : InfinitePlace F), Measure (Tor P w.Completion))
    (dtf : ∀ (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)), Measure (Tor P (Fv F v)))
    (dt : ∀ P : PPol σ r, Measure (Tor P (AF F))) (ht : ∀ P, IsTorusMeas P (dta P) (dtf P) (dt P))
    (K : GAd σ J → ℂ)
    (hK : K = fun x => ∑ᶠ δ : {δ : GRat σ J // Irreducible δ.1.1.charpoly}, tensor σ J fa ff (x⁻¹ * ratEmb σ J δ.1 * x))
    (t : PPol σ r → ℂ)
    (hterm : t = fun P => ((torVol P (dt P)).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf P v) (ff v)) *
      ∏ w, Phi (J := J) (μa w) (dta P w) (fa w)) :
    (∀ P, (torVol P (dt P) ≠ ⊤ ∧ (∀ v, PhiOK (J := J) (μf v) (dtf P v) (ff v)) ∧
      ∀ᶠ v in cofinite, Phi (J := J) (μf v) (dtf P v) (ff v) = 1) ∧ ∀ w, PhiOK (J := J) (μa w) (dta P w) (fa w)) ∧
    (Function.support t).Finite ∧ Integrable (descend (ratPts σ J) K) (quotMeasure (ratPts σ J) μ) ∧
      ∫ q, descend (ratPts σ J) K q ∂quotMeasure (ratPts σ J) μ = ∑ᶠ P, t P := by
  have ha' : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w), (ha w).1⟩
  have hc := (continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)).2
  obtain ⟨hfin, hfinx⟩ := GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hcm r J _ hc
  have hpol := fun P => GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals E F σ hcm hun r P J hJ L μa μf μ hμ fa ff ha' hf (dta P) (dtf P) (dt P) (ht P)
  have hinj : Function.Injective (Subtype.val : PPol σ r → E[X]) := Subtype.val_injective
  set S : Finset (PPol σ r) := (hfin.preimage (f := fun P : PPol σ r => P.1) hinj.injOn).toFinset with hSdef
  have hS : ∀ (x : GAd σ J) (γ : GRat σ J) (P : PPol σ r), tensor σ J fa ff (x⁻¹ * ratEmb σ J γ * x) ≠ 0 →
      γ.1.1.charpoly = P.1 → P ∈ S := fun x γ P h e =>
    (Finite.mem_toFinset _).2 ⟨γ, e, x, subset_tsupport _ h⟩
  have hsum : descend (ratPts σ J) K = fun q => ∑ P ∈ S, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q := by
    funext q
    rw [hK]
    refine finsum_group (fun γ : GRat σ J => γ.1.1.charpoly) _ hinj _ (fun γ => ⟨fun h => ?_, ?_⟩)
      (u := fun γ => tensor σ J fa ff ((Quotient.out q)⁻¹ * ratEmb σ J γ * Quotient.out q))
      ((hfinx (Quotient.out q)).subset fun γ h => subset_tsupport _ h) S (hS _)
    · obtain ⟨P, hP, -⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hcm r J hJ).2 γ h
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      rw [hP]
      exact P.2.2.1
  have hsupp : Function.support t ⊆ S := fun P hP => by
    by_contra hn
    refine hP ?_
    rw [hterm]
    refine (hpol P).2.symm.trans (integral_eq_zero_of_ae (.of_forall fun q => ?_))
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    by_contra h
    exact hn (hS _ δ.1 P h δ.2)
  refine ⟨fun P => ⟨⟨(GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 _ (ht P).haar, fun v => ?_, ?_⟩, fun w => ?_⟩,
    S.finite_toSet.subset hsupp, ?_, ?_⟩
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).1 v _ _ _ (hμ.haar_loc v) ((ht P).haar_loc v) (hf.1 v).1.continuous
      (hf.1 v).2
  · have := isLattice_stdLattice (E := Fld P) (n := 1)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hcm r P J hJ L, hf.2, hμ.eventually_eq_one,
      IsRestrictedProd.eventually_eq_one (ht P)] with v h1 h2 h3 h4
    have h5 := h1.2.2.2 (μf v) (dtf P v) (hμ.haar_loc v) ((ht P).haar_loc v) h3 h4
    rw [h2, Phi, finsum_eq_single _ ⟨1, h1.1⟩ fun q hq => (h5 q).2 fun e => hq (Subtype.ext e)]
    exact (h5 _).1 rfl
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).2 w _ _ _ (hμ.haar_arch w) ((ht P).haar_arch w) (ha' w).1 (ha' w).2
  · rw [hsum]
    exact integrable_finsetSum _ fun P _ => (hpol P).1
  · rw [hsum, integral_finsetSum _ fun P _ => (hpol P).1, finsum_eq_sum_of_support_subset _ hsupp, hterm]
    exact Finset.sum_congr rfl fun P _ => (hpol P).2

end GlobalTheory.TrEllSum
end
end
end
