module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOfDividingMaximalMinor
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulIsIntegralChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFTTNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsRegularAndUnitIffToric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormDividingWeightSumEqOfModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMem
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointOfRingHom

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_point_of_ringHom {o Ω K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] (M : RatModel o Ω)
    {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) (φ : M.ringOn U →+* K) :
    ∃ x : Sp K ⟶ M.Z, Set.range x ⊆ U ∧ (∀ a : M.ringOn U, φ a = M.val x a) ∧
      x ≫ M.s = spMap (φ.comp (algebraMap o _)) := by
  let ψ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (φ.comp (M.sectionsEquiv U hne).toRingHom)
  have hx := le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, valR (Spec.map ψ ≫ hU.fromSpec) U f = φ (M.sectionsEquiv U hne f) := fun f => by
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hr := (top_le_preimage_iff _ _).1 hx
  refine ⟨Spec.map ψ ≫ hU.fromSpec, hr, fun a => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := (M.sectionsEquiv U hne).surjective a
    rw [coe_sectionsEquiv, val_valF hr]
    exact (hv f).symm
  · rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← valR_constFn M.s _ U hx, hv]
    exact congrArg φ (Subtype.ext ((coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b)))

theorem exists_cen_of_ringHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsProper M.s → IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime]
    (y' : M.ringOn U →+* PadicAlgCl p), (∀ b : o, ‖y' (algebraMap o _ b)‖ ≤ 1) →
    ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z), M.Cen U z y ∧ ∀ a : M.ringOn U, y' a = M.val (gPt p ≫ y) a := by
  intro o Ω _ _ _ M U hs hU hne p _ y' hy'
  obtain ⟨x, hx, hv, hxs⟩ := M.exists_point_of_ringHom hU hne y'
  let σ : o →+* OO p := (y'.comp (algebraMap o _)).codRestrict (OO p).toSubring
    fun b => (mem_OO_iff _).2 (hy' b)
  obtain ⟨y, hy, -⟩ := exists_valuativeExtension (V := OO p) (K := PadicAlgCl p) M.s (spMap σ) x (by
    rw [hxs, ← Spec.map_comp]
    rfl)
  have hy2 : gPt p ≫ y = x := hy
  exact ⟨_, y, ⟨rfl, hy2 ▸ hx⟩, hy2 ▸ hv⟩

end GlobalTheory.ZH.RatModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDualBundleGeneratorsAllThetaTests

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

section Specialise

variable {o Ω K J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] [Fintype J]

theorem map_dotProduct_of_mem {B : Subalgebra o Ω} {f : Ω → K} (φ : B →+* K) (hf : ∀ x : B, φ x = f x)
    {u v : J → Ω} (hu : ∀ j, u j ∈ B) (hv : ∀ j, v j ∈ B) :
    f (u ⬝ᵥ v) = (fun j => f (u j)) ⬝ᵥ fun j => f (v j) := by
  have h : u ⬝ᵥ v = ((∑ j, (⟨u j, hu j⟩ : B) * ⟨v j, hv j⟩ : B) : Ω) := by
    simp [dotProduct]

  rw [h, ← hf, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hf, hf]

theorem dotProduct_mem_of_mem_span {σ : Type} [SetLike σ K] [SubringClass σ K] (O : σ) {s : Set (J → K)} {w v : J → K}
    (hs : ∀ x ∈ s, w ⬝ᵥ x ∈ O) (hv : v ∈ Submodule.span O s) : w ⬝ᵥ v ∈ O := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w ⬝ᵥ (c • x) = (c : K) * (w ⬝ᵥ x) := dotProduct_smul (c : K) w x
    rw [this]
    exact mul_mem c.2 hx


omit [Fintype J] in
theorem map_mem_span_of_mem_span {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K} (φ : B →+* K)
    (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type} {g : I → J → Ω}
    (hg : ∀ k j, g k j ∈ B) {v : J → Ω} (hv : v ∈ Submodule.span A (Set.range g)) :
    (∀ j, v j ∈ B) ∧ (fun j => f (v j)) ∈ Submodule.span O (Set.range fun k j => f (g k j)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨hg k, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    refine ⟨fun _ => zero_mem B, ?_⟩
    have h0 : f 0 = 0 := (hf 0).symm.trans (map_zero φ)
    have : (fun j => f ((0 : J → Ω) j)) = 0 := funext fun _ => h0
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun j => add_mem (hx.1 j) (hy.1 j), ?_⟩
    have : (fun j => f ((x + y) j)) = (fun j => f (x j)) + fun j => f (y j) := funext fun j =>
      (hf (⟨_, hx.1 j⟩ + ⟨_, hy.1 j⟩)).symm.trans (by rw [map_add (f := _), hf, hf]; rfl)
    rw [this]
    exact add_mem hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨fun j => mul_mem (hAB c.2) (hx.1 j), ?_⟩
    have : (fun j => f ((c • x) j)) = (⟨f c, hO c c.2⟩ : O) • fun j => f (x j) := funext fun j =>
      (hf (⟨_, hAB c.2⟩ * ⟨_, hx.1 j⟩)).symm.trans (by rw [map_mul, hf, hf]; rfl)
    rw [this]
    exact Submodule.smul_mem _ _ hx.2

theorem mem_span_map_iff_forall_dotProduct_mem [DecidableEq J] {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K}
    (φ : B →+* K) (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type}
    {g : I → J → Ω} (hg : ∀ k j, g k j ∈ B) (b : Matrix J J Ω)
    (hb : Submodule.span B (Set.range b) = Submodule.span B (Set.range fun i => Pi.single i (1 : Ω)))
    (H : ∀ w : J → Ω, w ∈ Submodule.span A (Set.range g) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range fun k j => f (g k j)) ↔
      ∀ v ∈ Submodule.span O ((fun (v : J → Ω) j => f (v j)) '' (Submodule.span A (Set.range b))), w ⬝ᵥ v ∈ O := by
  have hbB : ∀ i j, b i j ∈ B := fun i j => by
    have h : b i ∈ Submodule.span B (Set.range fun i => (Pi.single i (1 : Ω) : J → Ω)) :=
      hb ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
    rw [← hc]
    simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
  constructor
  · intro hw v hv
    refine dotProduct_mem_of_mem_span O ?_ hv
    rintro _ ⟨x, hx, rfl⟩
    rw [dotProduct_comm]
    refine dotProduct_mem_of_mem_span O ?_ hw
    rintro _ ⟨k, rfl⟩
    rw [dotProduct_comm, ← map_dotProduct_of_mem φ hf (hg k) (map_mem_span_of_mem_span hAB φ hf O hO hbB hx).1]
    exact hO _ ((H _).1 (Submodule.subset_span ⟨k, rfl⟩) x hx)
  · intro hw
    have h1 : ∀ i, ∃ c : J → B, ∑ l, HSMul.hSMul (c l) (b l) = (Pi.single i 1 : J → Ω) := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using h1
    let d : Matrix J J Ω := Matrix.of fun i l => (c i l : Ω)
    have hd : d * b = 1 := by
      ext i j
      have := congrFun (hc i) j
      simpa [Matrix.mul_apply, d, Finset.sum_apply, Subalgebra.smul_def, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have hd' : b * d = 1 := mul_eq_one_comm.1 hd
    have h2 : ∀ i, (fun j => d j i) ∈ Submodule.span A (Set.range g) := fun i => (H _).2 fun v hv => by
      refine dotProduct_mem_of_mem_span A ?_ hv
      rintro _ ⟨l, rfl⟩
      have : (fun j => d j i) ⬝ᵥ b l = (b * d) l i := dotProduct_comm _ _
      rw [this, hd', Matrix.one_apply]
      split_ifs
      exacts [one_mem A, zero_mem A]
    have h3 : ∀ i, w ⬝ᵥ (fun j => f (b i j)) ∈ O := fun i =>
      hw _ (Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h4 : ∀ j l, ∑ i, f (d j i) * f (b i l) = if j = l then 1 else 0 := fun j l => by
      have h := map_dotProduct_of_mem φ hf (u := d j) (v := fun i => b i l) (fun i => (c j i).2) (fun i => hbB i l)
      have h' : d j ⬝ᵥ (fun i => b i l) = (d * b) j l := rfl
      rw [h', hd, Matrix.one_apply] at h
      refine h.symm.trans ?_
      split_ifs
      exacts [(hf 1).symm.trans (map_one φ), (hf 0).symm.trans (map_zero φ)]
    have h5 : w = ∑ i, (⟨_, h3 i⟩ : O) • fun j => f (d j i) := by
      funext j
      have : ∀ i, ((⟨_, h3 i⟩ : O) • fun j => f (d j i)) j = ∑ l, w l * (f (d j i) * f (b i l)) := fun i => by
        show (w ⬝ᵥ (fun j => f (b i j))) * f (d j i) = _
        rw [dotProduct, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_apply, Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
      simp only [← Finset.mul_sum, h4]
      simp
    rw [h5]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (map_mem_span_of_mem_span hAB φ hf O hO hg (h2 i)).2


omit [Fintype J] in
theorem mem_span_iff_div_mem_span (O : ValuationSubring K) {I : Type} (G : I → J → K) {u : K} (hu : u ≠ 0)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range G) ↔ u⁻¹ • w ∈ Submodule.span O (Set.range fun k j => G k j / u) := by
  have key : ∀ (G : I → J → K) (s : K) (w : J → K), w ∈ Submodule.span O (Set.range G) →
      s • w ∈ Submodule.span O (Set.range fun k => s • G k) := fun G s w hw => by
    have := Submodule.mem_map_of_mem (f := (LinearMap.lsmul K (J → K) s).restrictScalars O) hw
    rwa [Submodule.map_span, ← Set.range_comp] at this
  have e : (fun k j => G k j / u) = fun k => u⁻¹ • G k := by
    funext k j
    simp [div_eq_inv_mul]
  rw [e]
  refine ⟨key G _ w, fun h => ?_⟩
  simpa [smul_smul, hu] using key _ u _ h

end Specialise

theorem exists_generators_at_all_tests : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG₀ : Fin n → S.J → S.R), S.Over₀ M U₀ → IsAffineOpen U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → S.IsEE M U₀ EE → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG₀ k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ (R' : Subalgebra o Ω) (hR : S.R ≤ R') (GG : Fin n → S.J → R'), R'.FG ∧ (∀ k j, (GG k j : Ω) = GG₀ k j) ∧ (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) := by
  intro o Ω _ _ _ _ S M U₀ EE n a GG₀ hO hU hsupp hEE hgen
  refine ⟨M.ringOn U₀, hO.le, fun k j => ⟨GG₀ k j, hO.le (GG₀ k j).2⟩, RatModel.fg_ringOn hU hO.ne,
    fun _ _ => rfl, fun p _ y' τ hy' w => ?_⟩
  obtain ⟨z, y, hz, hv⟩ := RatModel.exists_cen_of_ringHom o Ω M U₀ (projProper _ _ _ hO.proj) hU hO.ne p y' hy'
  have hAt : S.At M y (y'.comp (Subalgebra.inclusion hO.le).toRingHom) := fun r => hv ⟨r, hO.le r.2⟩
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hδ := ((hsupp z p y _ τ hz hAt).1 x₀).1 hx₀
  obtain ⟨V, b, hzV, -, hb⟩ := EE.loc z
  let ξ : M.Z := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξ : ξ ⤳ z := RatModel.gPt_specializes hz.1 _
  have hξU : ξ ∈ U₀ := hz.2 ⟨_, rfl⟩
  have hle : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξU
  let φ := RatModel.valHom (gPt p ≫ y) ξ (RatModel.range_eq_singleton _ _)
  have ht : S.th x₀ ∈ M.O ξ := hle (hO.le (S.th_mem x₀))
  have ht' : (S.th x₀)⁻¹ ∈ M.O ξ := hle (hO.th_unit x₀ hx₀.1)
  have hg : ∀ k j, (GG₀ k j : Ω) / S.th x₀ ^ a ∈ M.O ξ := fun k j => by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (hle (hO.le (GG₀ k j).2)) (pow_mem ht' a)
  have H := hgen z x₀ hx₀
  have hE := hEE.2 z p y _ τ hz hAt
  rw [hb z hzV] at H hE
  have key := mem_span_map_iff_forall_dotProduct_mem (RatModel.O_le_of_specializes hξ) φ (fun _ => rfl) (OO p)
    (fun x hx => (mem_OO_iff _).2 (RatModel.norm_val_le_one hz.1 hx)) hg b
    ((hb ξ (hξ.mem_open V.isOpen hzV)).symm.trans (hEE.1 ξ hξU)) H
  set u := M.val (gPt p ≫ y) (S.th x₀) with hu
  have hu0 : u ^ a ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 (hδ ▸ τ.δ_pos))
  have e : (fun k j => y' ⟨GG₀ k j, hO.le (GG₀ k j).2⟩ / u ^ a) =
      fun k j => M.val (gPt p ≫ y) ((GG₀ k j : Ω) / S.th x₀ ^ a) := by
    funext k j
    rw [div_eq_iff hu0, hv]
    have h := map_mul φ ⟨_, hg k j⟩ (⟨_, ht⟩ ^ a)
    rw [map_pow] at h
    refine Eq.trans ?_ h
    exact congrArg (M.val (gPt p ≫ y)) (div_mul_cancel₀ _ (pow_ne_zero a hx₀.1)).symm
  rw [mem_span_iff_div_mem_span (OO p) _ hu0, e]
  refine (key _).trans ?_
  rw [← hE]
  refine forall₂_congr fun v _ => ?_
  rw [mem_OO_iff, smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, norm_pow, hδ,
    inv_mul_le_iff₀ (pow_pos τ.δ_pos a), _root_.mul_one]

end GlobalTheory.ZH
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable (S : ThetaSys o Ω)

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH

open MinorModel

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_ringOn_contains_of_fg_of_finite {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (A : Subalgebra o Ω) (hA : A.FG) (F : Set Ω)
    (hF : F.Finite) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ A ≤ M.ringOn U ∧ ∀ x ∈ F, x ∈ M.ringOn U := by
  obtain ⟨s, rfl⟩ := hA
  have hT : ((s : Set Ω) ∪ F).Finite := s.finite_toSet.union hF
  let U : M.Z.Opens := ⟨⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z},
    hT.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x⟩
  have hU : ∀ x ∈ (s : Set Ω) ∪ F, x ∈ M.ringOn (U : Set M.Z) := fun x hx =>
    _root_.GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z hz =>
      Set.mem_iInter₂.1 hz x hx
  refine ⟨U, ⟨genericPoint M.Z, ?_⟩, ?_, fun x hx => hU x (Or.inr hx)⟩
  · show genericPoint M.Z ∈ ⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z}
    simp [M.O_genericPoint]
  · exact Algebra.adjoin_le fun x hx => hU x (Or.inl hx)

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_over0_ringOn_of_fg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (S : _root_.GlobalTheory.ZH.ThetaSys o Ω) (M : _root_.GlobalTheory.ZH.RatModel o Ω) (R' : Subalgebra o Ω)
    (hfg : R'.FG) (hR : S.R ≤ R') (hn : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) (hd : M.HasDiv S.th) :
    ∃ U : M.Z.Opens, S.Over₀ M U ∧ R' ≤ M.ringOn U := by
  obtain ⟨U, hUne, hAU, hFU⟩ := exists_open_ringOn_contains_of_fg_of_finite M R' hfg
    (Set.range (fun x => (S.th x)⁻¹) ∪ Set.range (fun q : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => (S.FF q.1 q.2.1 q.2.2)⁻¹))
    ((Set.finite_range _).union (Set.finite_range _))
  exact ⟨U, ⟨hn, hp, hd, hUne, hR.trans hAU, fun x _ => hFU _ (Or.inl ⟨x, rfl⟩),
    fun T c k _ _ => hFU _ (Or.inr ⟨⟨T, c, k⟩, rfl⟩)⟩, hAU⟩

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem module_finite_of_subfield_le {Ω : Type} [Field Ω] {K K' : Subfield Ω} (h : K ≤ K')
    [Module.Finite K Ω] : Module.Finite K' Ω := by
  letI : Algebra K K' := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite K K' Ω

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem isProper_of_isProjOver_degeneration {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) : IsProper M.s := by
  obtain ⟨N, i, hi, e⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o N
  rw [← e]
  infer_instance


open CategoryTheory Limits AlgebraicGeometry in
open Classical in
theorem _root_.GlobalTheory.ZH.exists_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [_root_.GlobalTheory.ZH.ArithBase o Ω] (S : _root_.GlobalTheory.ZH.ThetaSys o Ω), S.HasTests →
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω →
    ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : _root_.GlobalTheory.ZH.RatModel o Ω) (U₀ : Z.Z.Opens)
      (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver X.s ∧
      Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧
      S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧
      (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧
      (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω,
        w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔
          ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧
      ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z,
        (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧
        (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧
          S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  intro o Ω _ _ _ _ S hT hfin
  haveI : Algebra.FiniteType ℤ o := _root_.GlobalTheory.ZH.ArithBase.ft (o := o) Ω
  haveI : CharZero Ω := _root_.GlobalTheory.ZH.ArithBase.char o (Ω := Ω)
  haveI : IsDedekindDomain o := _root_.GlobalTheory.ZH.ArithBase.ded (o := o) Ω
  have hwt := _root_.GlobalTheory.ZH.test_weights o Ω S
  obtain ⟨M₁, U₁, hAdm₁, hAff₁, -⟩ := _root_.GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S Unit (fun _ => 1) ⟨(), one_ne_zero⟩
    (by
      rw [show {x | ∃ i j : S.Gam × Unit, x = S.th j.1 * (fun _ => (1:Ω)) j.2 / (S.th i.1 * (fun _ => (1:Ω)) i.2)}
          = {x | ∃ i j, x = S.th j / S.th i} by ext x; simp]
      exact hfin)
  have hO₁ := hAdm₁.1
  have hreg₁ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω M₁ U₁ hO₁.normal
  have htst₁ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S M₁ U₁ hT hO₁
  have hsup₁ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M₁ U₁ hO₁
  have hiso₁ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁
  obtain ⟨EE₁, hEE₁, hspan₁⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_adm o Ω S M₁ U₁ hT hAdm₁
  have hFF₁ := _root_.GlobalTheory.ZH.FF_TT_ne_zero o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hdot₁ := _root_.GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hnorm := _root_.GlobalTheory.thetaSys_norm_FF_le_exp o Ω S hwt
  have hnd₁ := _root_.GlobalTheory.norm_val_FF_eq_of_div o Ω S M₁ U₁ hO₁ hsup₁ hnorm htst₁
  have hdot₁' := hdot₁ hnorm hnd₁ hFF₁ hspan₁
  obtain ⟨n, a, GG₀, hGG₀⟩ := _root_.GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁.2 hiso₁ hFF₁ hspan₁ hdot₁'
  obtain ⟨R', hR, GG, hfg, hGGeq, htests⟩ := _root_.GlobalTheory.ZH.exists_generators_at_all_tests o Ω S M₁ U₁ EE₁ n a GG₀ hO₁ hAff₁ hsup₁ hEE₁ hGG₀
  have hinj : Function.Injective (algebraMap o Ω) := (inferInstance : _root_.GlobalTheory.ZH.ArithBase o Ω).4
  obtain ⟨X, hXn, hXp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj S.Gam S.th S.th_ne hfin
  have hXnorm := hXn.isNormalScheme
  obtain ⟨UX, hOX, hRX⟩ := exists_open_over0_ringOn_of_fg S X R' hfg hR hXnorm hXp hXn.1
  have hregX := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω X UX hXnorm
  have htstX := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S X UX hT hOX
  have hsupX := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S X UX hOX
  have hisoX := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S X UX hOX hregX htstX hsupX
  have hminX := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S X UX R' hR n a GG hOX hRX hregX htstX hsupX hisoX hwt htests
  obtain ⟨ξ, hξ⟩ := hOX.ne
  obtain ⟨x₀, hx₀⟩ := hXn.1 ξ
  obtain ⟨k₀, hk₀, -⟩ := ((hminX ξ x₀ hx₀).2).1 (hisoX.2.2.1 ξ hξ)
  obtain ⟨Z, hZn, hZp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj (S.Gam × (S.J → Fin n))
    (fun q => S.th q.1 * Matrix.det (Matrix.of fun i j => (GG (q.2 i) j : Ω)))
    ⟨(x₀, k₀), mul_ne_zero hx₀.1 hk₀⟩
    (by
      haveI := hfin
      refine module_finite_of_subfield_le (K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j, x = S.th j / S.th i})) ?_
      refine Subfield.closure_le.2 (Set.union_subset (fun x hx => Subfield.subset_closure (Or.inl hx)) ?_)
      rintro x ⟨i, j, rfl⟩
      exact Subfield.subset_closure (Or.inr ⟨(i, k₀), (j, k₀), (mul_div_mul_right _ _ hk₀).symm⟩))
  have hZdiv := (_root_.GlobalTheory.ZH.isNm_normal_and_div_prod o Ω Z S.Gam S.th).2.1 (S.J → Fin n)
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)))
  have hZth : Z.HasDiv S.th := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨i, ((hZdiv i k z).1 h).1⟩
  have hZd : Z.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨k, ((hZdiv i k z).1 h).2⟩
  have hZnorm := hZn.isNormalScheme
  obtain ⟨UZ, hOZ, hRZ⟩ := exists_open_over0_ringOn_of_fg S Z R' hfg hR hZnorm hZp hZth
  have hregZ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω Z UZ hZnorm
  have htstZ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S Z UZ hT hOZ
  have hsupZ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S Z UZ hOZ
  have hisoZ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S Z UZ hOZ hregZ htstZ hsupZ
  obtain ⟨EE, hEE, hspanZ⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_hasDiv_minors o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ htests hZd
  have hminZ := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ hisoZ hwt htests
  obtain ⟨f, hf⟩ := hXn.exists_isHom (φ := AlgHom.id o Ω)
    (show Z.HasDiv (fun j => (AlgHom.id o Ω) (S.th j)) from hZth)
    (fun z => _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hZnorm z)
  let Xab : X.Z.Opens := ⟨{x | S.TT X x = ⊥}, by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨y₀, hy₀⟩ := hXn.1 x
    obtain ⟨k, hk, hmem⟩ := ((hminX x y₀ hy₀).2).1 hx
    refine ⟨{y | X.Div S.th y₀ y} ∩ {y | S.th y₀ ^ (a * Fintype.card S.J) /
      Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) ∈ X.O y}, ?_,
      (X.isOpen_setOf_div S.th y₀).inter
        (X.isOpen_setOf_mem_O _), hy₀, hmem⟩
    rintro y ⟨hy1, hy2⟩
    exact ((hminX y y₀ hy1).2).2 ⟨k, hk, hy2⟩⟩
  have hiso := _root_.GlobalTheory.ZH.isIso_morphismRestrict_of_isNm_prod o Ω X Z S.Gam (S.J → Fin n) S.th
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) f hXn hZn (isProper_of_isProjOver_degeneration Z hZp) hf Xab (by
      intro z hz
      obtain ⟨y₀, hy₀⟩ := hXn.1 z
      obtain ⟨k, hk, hmem⟩ := ((hminX z y₀ hy₀).2).1 hz
      refine ⟨k, hk, fun j => ?_⟩
      have h1 := (hminX z y₀ hy₀).1 j
      have ht : S.th y₀ ^ (a * Fintype.card S.J) ≠ 0 := pow_ne_zero _ hy₀.1
      have h2 := (X.O z).mul_mem h1 hmem
      beta_reduce at h1 hmem h2 ⊢
      rwa [div_mul_div_cancel₀ ht] at h2)
  exact ⟨n, a, fun k j => (GG k j : Ω), X, Z, UZ, EE, f, Xab, hXn, hXp, hZn, hOZ, hEE, hf, rfl, hiso, hspanZ, hminZ⟩

end GlobalTheory.ZH
end
end
