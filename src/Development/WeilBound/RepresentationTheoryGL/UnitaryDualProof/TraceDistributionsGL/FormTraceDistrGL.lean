module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTrace
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.KirillovEndUnitaryOfTheoremA
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
import GroundTheory.AutomorphicForms.HeckeIrreducible
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.MeasuresGL

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTraceEq

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Eq

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {g : G} {K : Subgroup G} {x : G} : x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  simp [conjSub, MulAut.conj_apply]

def conjHomeo (g : G) : G ≃ₜ G := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)

theorem coe_conjSub (g : G) (K : Subgroup G) : (conjSub g K : Set G) = conjHomeo g ⁻¹' (K : Set G) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, mem_conjSub, conjHomeo, Homeomorph.trans_apply,
    Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]

theorem isCompact_conjSub (g : G) {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    IsCompact (conjSub g K : Set G) := by
  rw [coe_conjSub, ← congrFun (conjHomeo g).image_symm (K : Set G)]
  exact hKc.image (conjHomeo g).symm.continuous

theorem isOpen_conjSub (g : G) {K : Subgroup G} (hKo : IsOpen (K : Set G)) : IsOpen (conjSub g K : Set G) := by
  rw [coe_conjSub]
  exact hKo.preimage (conjHomeo g).continuous

def conjEquiv (g : G) (K : Subgroup G) : fixedVectors ρ K ≃ₗ[ℂ] fixedVectors ρ (conjSub g K) where
  toFun v := ⟨ρ g v, by
    rw [mem_fixedVectors]
    intro x hx
    have h := v.2
    rw [mem_fixedVectors] at h
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, h _ (mem_conjSub.1 hx)]⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  invFun w := ⟨ρ g⁻¹ w, by
    rw [mem_fixedVectors]
    intro x hx
    have h := w.2
    rw [mem_fixedVectors] at h
    have hx' : g * x * g⁻¹ ∈ conjSub g K := mem_conjSub.2 (by group; exact hx)
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g),
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, h _ hx']⟩
  left_inv v := Subtype.ext (by
    show ρ g⁻¹ (ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  right_inv w := Subtype.ext (by
    show ρ g (ρ g⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem conjEquiv_apply (g : G) (K : Subgroup G) (v : fixedVectors ρ K) :
    (conjEquiv g K v : V) = ρ g v := rfl

theorem conjEquiv_symm_apply (g : G) (K : Subgroup G) (w : fixedVectors ρ (conjSub g K)) :
    ((conjEquiv g K).symm w : V) = ρ g⁻¹ w := rfl

theorem biInv_conj (g : G) {K : Subgroup G} {f : G → ℂ} (hf : BiInv K f) : BiInv (conjSub g K) (conjFn g f) := by
  intro k hk x
  have hk' := mem_conjSub.1 hk
  constructor
  · show f (g⁻¹ * (k * x) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).1
    rw [← this]; congr 1; group
  · show f (g⁻¹ * (x * k) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).2
    rw [← this]; congr 1; group

theorem formD_equiv [μ.IsMulRightInvariant] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (g : G) (B : Sesq V) (f : G → ℂ)
    (hf : f ∈ testFn G) :
    formD μ hρ hpos hinv Pr ((B ∘ₗ ρ g).compl₂ (ρ g)) f = formD μ hρ hpos hinv Pr B (conjFn g f) := by
  have hcoe : ((biTranslL g g (⟨f, hf⟩ : testFn G) : testFn G) : G → ℂ) = conjFn g f := by
    ext x
    simp [biTranslL, conjFn]
  have h1 : Pr f = ⟨f, hf⟩ := hPr ⟨f, hf⟩
  have h2 : Pr (conjFn g f) = biTranslL g g (⟨f, hf⟩ : testFn G) := by
    rw [← hcoe]
    exact hPr _
  rw [formD_apply, formD_apply, h1, h2]
  obtain ⟨K, hKc, hKf⟩ := exists_K (⟨f, hf⟩ : testFn G)
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have hK'c := isCompact_conjSub g hKc
  have hK'o := isOpen_conjSub g hKo
  have hK'f : BiInv (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G) : G → ℂ) := by
    rw [hcoe]
    exact biInv_conj g hKf
  rw [DF_eq μ hρ hpos hinv _ _ hKc hKo hKf, DF_eq μ hρ hpos hinv _ _ hK'c hK'o hK'f]
  haveI := hρ.2 _ hKc hKo
  haveI := hρ.2 _ hK'c hK'o
  have hR : rN μ hρ hpos hK'c hK'o B (biTranslL g g (⟨f, hf⟩ : testFn G)) =
      (conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) := by
    apply riesz_unique hpos (rN_spec μ hρ hpos hK'c hK'o B _)
    intro x' y'
    have hs := rN_spec μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
      ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x') ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y')
    have ex : (((conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) x' : fixedVectors ρ _) : V) =
        ρ g (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
          ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [LinearEquiv.conj_apply_apply, conjEquiv_apply]
    have ey : (y' : V) = ρ g ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y') := by
      rw [← conjEquiv_apply, LinearEquiv.apply_symm_apply]
    have eA : resA μ hρ (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G)) x' =
        ρ g (heckeAct μ ρ f ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [conjEquiv_symm_apply]
      simp only [resA, LinearMap.comp_apply, Submodule.subtype_apply, heckeLin_apply]
      exact heckeAct_biTranslL μ hρ.1 g _ _
    rw [ex, ey, hinv, eA]
    simpa [resA, heckeLin_apply] using hs
  simp only [DK]
  rw [hR, LinearMap.trace_conj']

end Eq

end PositivityTheory.PfBern.Unit
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.HasTraceDistrOfAdmissible

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_testProj : ∃ Pr : (G → ℂ) →ₗ[ℂ] testFn G, ∀ f : testFn G, Pr f = f := by
  obtain ⟨Pr, hPr⟩ := LinearMap.exists_leftInverse_of_injective (testFn G).subtype (Submodule.ker_subtype _)
  exact ⟨Pr, fun f => LinearMap.congr_fun hPr f⟩

end Gen

end PositivityTheory.PfBern.Unit
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.LevelSmulSmul

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

section Level

variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

theorem level_smul_smul (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    (c • h) • w = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  rw [HeckeAlgebra.coe_smul]
  exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))

theorem level_smul_comm (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    h • (c • w) = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (c • (w : V)) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo w.2))

theorem level_schur (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (φ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) :
    ∃ c : ℂ, ∀ w, φ w = c • w := by
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let φℂ : Module.End ℂ (fixedVectors ρ K) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c w => by
        have e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w := by
          rw [level_smul_smul, one_smul]
        rw [RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }
  have hnt : Nontrivial (fixedVectors ρ K) := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φℂ
  obtain ⟨w₀, hw₀⟩ := hc.exists_hasEigenvector
  let ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) :=
    { toFun := fun w => φ w - c • w
      map_add' := fun a b => by rw [map_add (f := _), smul_add]; abel
      map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }
  have hw₀ker : w₀ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    show φ w₀ - c • w₀ = 0
    rw [sub_eq_zero]
    exact Module.End.mem_eigenspace_iff.1 hw₀.1
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)
  have htop := (eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ LinearMap.ker ψ := by rw [htop]; exact Submodule.mem_top
  exact sub_eq_zero.1 hw

theorem level_density (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (A : Module.End ℂ (fixedVectors ρ K)) :
    ∃ r : HeckeAlgebraLevel μ K hKc hKo, levelLin hKc hKo ρ r = A := by
  classical
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let fE : Module.End (Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) (fixedVectors ρ K) :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun φ w => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        obtain ⟨c, hc⟩ := level_schur hKc hKo hρ hK φ
        rw [hc, hc, A.map_smul] }
  let b := Module.finBasis ℂ (fixedVectors ρ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this.symm

end Level

end Faith

end PositivityTheory.PfBern.Unit
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FormTraceDistrGL

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory PositivityTheory.PfBern.Unit

namespace PositivityTheory.RgUd.AB.Pf

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem formD_faithful [ρ.IsIrreducible] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (C : Sesq V)
    (h : ∀ f ∈ testFn G, formD μ hρ hpos hinv Pr C f = 0) : C = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun u => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, LinearMap.zero_apply]
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have huW : u ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  set W := fixedVectors ρ (K : Subgroup G)
  let vW : W := ⟨v, hvW⟩
  let uW : W := ⟨u, huW⟩
  let φ : W →ₗ[ℂ] ℂ := (B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : Module.End ℂ W := φ.smulRight vW
  obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW A
  let rf : locallyConstantCompactSupport G ℂ ℂ := (r : HeckeAlgebra μ)
  have hbi : BiInv (K : Subgroup G) (rf : G → ℂ) := fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x
  have hf := h rf rf.2
  rw [formD_apply, hPr rf] at hf
  change DF μ hρ hpos C rf = 0 at hf
  rw [DF_eq μ hρ hpos hinv C _ hKc hKo hbi] at hf
  have hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v := by
    intro x
    have e := congrArg (fun T : Module.End ℂ W => (T x : V)) hr
    rw [← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]
    rfl
  have huu : (B₀ u u) ≠ 0 := fun e => by
    have := hpos u hu0
    rw [e] at this
    simp at this
  set N := rN μ hρ hpos hKc hKo C rf with hN
  have sN := rN_spec μ hρ hpos hKc hKo C rf
  let m : W := (B₀ u u)⁻¹ • N uW
  have hm : ∀ y : W, B₀ (m : V) y = C v y := by
    intro y
    have := sN uW y
    rw [hres] at this
    show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y
    rw [map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ huu, one_mul]
  have hNe : N = φ.smulRight m := by
    refine riesz_unique hpos sN fun x y => ?_
    show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y
    rw [hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]
    rfl
  unfold DK at hf
  rw [← hN, hNe, LinearMap.trace_smulRight] at hf
  have : φ m = C v u := hm uW
  rw [← this]
  exact hf

end Faith

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem formTraceDistrGL : FormTraceDistrGL k := by
  intro n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := GL (Fin (n + 1)) k)
  exact ⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf,
    fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩

theorem theoremA_of_thmA (hA : PositivityTheory.RgUd.ThmA k) : TheoremA k := by
  intro n D hD g f hf
  have hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)) := ⟨hf, Set.subset_univ _⟩
  have hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)),
      D (fun x => f (p * x * p⁻¹)) = D f := by
    intro p hp f hf
    have := hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1
    have e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹) := by
      funext x; unfold conjFn; rw [inv_inv]
    rw [← e]; exact this
  have := hA n D hP g⁻¹ f hf'
  have e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹) := by
    funext x; unfold conjFn; rw [inv_inv]
  rw [e]; exact this

theorem thmB_of_kirillov (hK : KirillovForm k) : PositivityTheory.RgUd.ThmB k := by
  intro n V _ _ π hs hirr B hB β hβ
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)
  obtain ⟨c, hc⟩ := hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ
  exact ⟨c, fun v w => by rw [hc]; rfl⟩

theorem thmB (hA : PositivityTheory.RgUd.ThmA k) : PositivityTheory.RgUd.ThmB k :=
  thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))

end PositivityTheory.RgUd.AB.Pf
end
end
end
