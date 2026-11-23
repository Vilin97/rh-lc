module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataDefiniteLiftLatticeBaseChangeStatement
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMapStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtende
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.W1idxUnionW1jwFinite
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChange

section

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.DualBC

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem mem_dual_iff {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (A : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]


omit [NumberField K] in
theorem hform_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    Formalism.DivisionValues.hform H x y = ∑ j, star (x j) * (H.mulVec y) j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring


omit [NumberField K] in
theorem star_int (c : 𝓞 K) : algebraMap (𝓞 K) K (Formalism.DivisionValues.cO K c) = star (algebraMap (𝓞 K) K c) := rfl


omit [StarRing K] in
theorem exists_extend {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A)
    (f : A →ₗ[𝓞 K] 𝓞 K) :
    ∃ F : (Fin d → K) →ₗ[K] K, ∀ x : A, F x = algebraMap (𝓞 K) K (f x) := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs, b, hb, hsA⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom (R := 𝓞 K) b A hA.fg
  have hbA : ∀ i, b i ∈ A := fun i => by rw [hb i]; exact hsA i.2
  let F : (Fin d → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩))
  let F' : A →ₗ[𝓞 K] K := (F.restrictScalars (𝓞 K)).comp A.subtype
  let g' : A →ₗ[𝓞 K] K := (Algebra.linearMap (𝓞 K) K).comp f
  let P : Submodule (𝓞 K) (Fin d → K) := (LinearMap.eqLocus F' g').map A.subtype
  have hspan : Submodule.span (𝓞 K) (Set.range b) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨b i, hbA i⟩, ?_, rfl⟩
    show F (b i) = algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩)
    exact b.constr_basis K _ i
  refine ⟨F, fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hspan (hc x x.2)
  have hz' : z = c • x := Subtype.ext (by simpa using hzx)
  have hzF : F' z = g' z := hz
  rw [hz', map_smul, map_smul] at hzF
  simp only [F', g', LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, Algebra.smul_def] at hzF
  exact mul_left_cancel₀ (by simpa using hc0) hzF

theorem exists_family {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (hH : IsUnit H.det)
    (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    ∃ (n : ℕ) (a b : Fin n → Fin d → K), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) ∧
      ∀ y, y = ∑ i, Formalism.DivisionValues.hform H (a i) y • b i := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := K) A hA.fg hinj
  choose F hF using fun i => exists_extend A hA (f i)
  let w : Fin n → Fin d → K := fun i => H⁻¹.mulVec (fun j => star (F i (Pi.single j 1)))
  have hFcoord : ∀ i (y : Fin d → K), F i y = ∑ j, y j * F i (Pi.single j 1) := by
    intro i y
    conv_lhs => rw [← Finset.univ_sum_single y]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (y j) : Fin d → K) = y j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul]
  have hw : ∀ i (y : Fin d → K), Formalism.DivisionValues.hform H y (w i) = star (F i y) := by
    intro i y
    rw [hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, hFcoord,
      star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
  have hexp : ∀ y : Fin d → K, y = ∑ i, F i y • (g i : Fin d → K) := by
    have hT : (∑ i, (F i).smulRight (g i : Fin d → K)) = LinearMap.id := by
      refine LinearMap.ext_on hA.span_eq_top fun x hx => ?_
      have h1 := congrArg (fun v : A => (v : Fin d → K)) (hgf ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      conv_rhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hF i ⟨x, hx⟩, algebraMap_smul]
    intro y
    have := LinearMap.congr_fun hT y
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at this
    exact this.symm
  have hnd : ∀ z : Fin d → K, (∀ u, Formalism.DivisionValues.hform H u z = 0) → z = 0 := by
    intro z hz
    have hHz : H.mulVec z = 0 := by
      ext i
      have := hz (Pi.single i 1)
      rw [hform_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul _ hH, ← Matrix.mulVec_mulVec, hHz,
      Matrix.mulVec_zero]
  refine ⟨n, fun i => (g i : Fin d → K), w, fun i => (g i).2, fun i => ?_, fun y => ?_⟩
  · rw [mem_dual_iff]
    intro y hy
    refine ⟨Formalism.DivisionValues.cO K (f i ⟨y, hy⟩), ?_⟩
    rw [star_int, hw, hF i ⟨y, hy⟩]
  · refine (sub_eq_zero.1 (hnd _ fun u => ?_)).symm

    rw [map_sub, sub_eq_zero, map_sum]
    conv_rhs => rw [hexp u]

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hw, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_comm]

theorem dual_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  intro K K' _ _ _ _ _ _ φ d d' G hG H H' hHH' hH A hA
  classical
  set ι : (Fin d → K) → (Fin d' → K') := fun x => Matrix.mulVec G fun k => φ (x k) with hι
  have ι_add : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y
    simp only [hι, Pi.add_apply, map_add (f := _)]
    rw [← Matrix.mulVec_add]
    rfl
  have ι_smul : ∀ (c : K) x, ι (c • x) = φ c • ι x := by
    intro c x
    simp only [hι, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have ι_sum : ∀ {m : ℕ} (v : Fin m → Fin d → K), ι (∑ i, v i) = ∑ i, ι (v i) := by
    intro m v

    simp only [hι, Finset.sum_apply, map_sum]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext k
    simp [Finset.sum_apply]
  have ι_single : ∀ k : Fin d, ι (Pi.single k 1) = G.mulVec (Pi.single k 1) := by
    intro k
    simp only [hι]
    congr 1
    ext j
    by_cases hj : j = k <;> simp [hj]
  have hspanι : Submodule.span K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨v, rfl⟩ := hG.2 z
    rw [← Finset.univ_sum_single v, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show (Pi.single k (v k) : Fin d → K') = v k • Pi.single k 1 by
      ext j; by_cases hj : j = k <;> simp [hj], Matrix.mulVec_smul, ← ι_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hιH : ∀ x y, Formalism.DivisionValues.hform H' (ι x) (ι y) = φ (Formalism.DivisionValues.hform H x y) := hHH'
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, b, ha, hb, hab⟩ := exists_family H hH A hA
    have hT : (∑ i, (Formalism.DivisionValues.hform H' (ι (a i))).smulRight (ι (b i))) = LinearMap.id := by
      refine LinearMap.ext_on hspanι ?_
      rintro _ ⟨y, rfl⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hιH]
      conv_rhs => rw [hab y]
      rw [ι_sum]
      simp only [ι_smul]
    have hx' : x = ∑ i, Formalism.DivisionValues.hform H' (ι (a i)) x • ι (b i) := by
      have := LinearMap.congr_fun hT x
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply] at this
      exact this.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := (mem_dual_iff H' _ x).1 hx (ι (a i))
      (Submodule.subset_span ⟨a i, ha i, rfl⟩)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨c, hc⟩ := (mem_dual_iff H A z).1 hz y hy
      refine ⟨RingOfIntegers.mapRingHom φ c, ?_⟩
      rw [hιH, ← hc]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hc₁, hc₂]⟩
    | smul r y _ h =>
      obtain ⟨c, hc⟩ := h
      refine ⟨Formalism.DivisionValues.cO K' r * c, ?_⟩
      rw [← algebraMap_smul K' r y, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hc,
        star_int, starRingEnd_apply]

end GlobalTheory.Mem.DualBC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtendeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.liftFormsLattice_definiteLattice_baseChange_extended : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  first | exact @GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt | exact GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt | (intros; apply GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZeroContentPlacesIffOverOfNonvanishing

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespond

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem exists_hom_of_range {K K' : Type} [Field K] [Field K'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (h : Set.range σ ⊆ Set.range σ') :
    ∃ φ : K →+* K', ∀ x, σ' (φ x) = σ x := by
  choose g hg using fun x => h ⟨x, rfl⟩
  exact ⟨{ toFun := g
           map_one' := σ'.injective (by rw [hg, map_one, map_one])
           map_mul' := fun a b => σ'.injective (by rw [map_mul σ', hg, hg, hg, map_mul])
           map_zero' := σ'.injective (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => σ'.injective (by rw [map_add σ', hg, hg, hg, map_add (f := _)]) }, hg⟩



theorem extendedData_nonzero_index_places_correspond : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.liftFormsLattice_definiteLattice_baseChange_extended h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.extendedData_definiteLiftLattice_baseChange h1 h2 h3 h4 h5 h6 h7)) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hIJ B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt v v' hB
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  obtain ⟨φ, hφ⟩ := exists_hom_of_range (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hE.2.2.2
  have hok := hHL.ok.ok2
  refine mem_zeroContentPlaces_iff_over_of_nonvanishing z z' hm (fun j j' hj P P' hPP => ?_) v v' hB
  have hP : ∀ (x : 𝓞 (w.st Z).toD7.what₂.LL) (x' : 𝓞 (w'.st Z').toD7.what₂.LL), φ (x : (w.st Z).toD7.what₂.LL) = (x' : (w'.st Z').toD7.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal) := fun x x' e => hPP x x' (by rw [← e, hφ])
  have hT : Submodule.IsLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) := Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr
  have hTfull : Submodule.IsFullLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :=
    Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr
  have hH : IsUnit (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).det := Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr
  obtain ⟨G, hG1, hG2, hG3⟩ := hIJ.1 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨N, hN1, hN2, hN3⟩ := hIJ.2 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  refine nzAt_iff_of z z' j j' P P' ?_ ?_
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ G hG1 P P' hP ((s0Of z.R z.F).M j)
      (Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (hHL.mLat j).fg (hT.fg.map _)
    rw [← hG2, ← hG3] at k
    exact k
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ N hN1 P P' hP _ _ hT.fg (GlobalTheory.Mem.NonzeroPlacesOverPrimes.dual_fg _ hH _ hTfull)
    rw [← GlobalTheory.Mem.DualBC.dual_baseChange _ _ φ _ _ N hN1 _ _ hN3 hH _ hTfull, ← hN2] at k
    exact k

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end
end
