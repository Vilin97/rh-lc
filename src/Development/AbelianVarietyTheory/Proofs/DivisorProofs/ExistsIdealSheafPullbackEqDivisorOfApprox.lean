module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChevalleyCorrectionOverProperFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPointStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.AlgebraicGeometry.QuasiAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierIdealSheafLeOfClosedPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints : ∀ (X : Scheme.{0}) [CompactSpace X] (D : EffCartierData X) (K : X.IdealSheafData), (∀ x : X, IsClosed ({x} : Set X) → ∃ (W : X.affineOpens) (i : D.ι) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG X h (D.f i) ∈ K.ideal W) → D.idealSheaf ≤ K := by
  intro X _ D K hK
  have hc : ∀ y : X, ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x := fun y => by
    obtain ⟨x, hx, hxc⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
    exact ⟨x, hxc, specializes_iff_mem_closure.2 hx⟩
  choose x hxc hyx using hc
  choose W i h hxW hmem using fun y => hK (x y) (hxc y)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun y _ =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨y, (hyx y).mem_open (W y).1.isOpen (hxW y)⟩)
    fun y => ?_
  rw [D.ideal_idealSheaf (W y) (i y) (h y), Ideal.span_singleton_le_iff_mem]
  exact hmem y
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc

theorem resG_f_mem_comap_map_ideal (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω)
    (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π) (D : EffCartierData M.Z) (V : M₁.Z.affineOpens)
    (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι) (hxV : π x ∈ V.1) (hxi : x ∈ D.U i)
    (hg : g ∈ (D.idealSheaf.map π).ideal V) (hG : valF M₁.pt V.1 g ≠ 0)
    (hO : valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x) :
    ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧
      resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  obtain ⟨U, s, hUa, hxU, hUle, hs⟩ :=
    RatModel.exists_affine_of_mem_O hO (V := D.U i ⊓ π ⁻¹ᵁ V.1) ⟨hxi, hxV⟩
  have hUi : U ≤ D.U i := hUle.trans inf_le_left
  have hUV : U ≤ π ⁻¹ᵁ V.1 := hUle.trans inf_le_right
  have hUne : (U : Set M.Z).Nonempty := ⟨x, hxU⟩
  have hmem := (GlobalTheory.Cartier.comap_le_iff (D.idealSheaf.map π) π ((D.idealSheaf.map π).comap π)).1 le_rfl
    V g hg ⟨U, hUa⟩ hUV
  refine ⟨⟨U, hUa⟩, hUi, hxU, ?_⟩
  have key : resG M.Z hUi (D.f i) = s * resG M.Z hUV ((π.app V.1).hom g) := by
    apply M.valF_injective hUne
    rw [← M.res_apply U hUne (s * _), map_mul, M.res_apply, M.res_apply, M.valF_resG hUi hUne,
      M.valF_resG hUV hUne, hs]
    have h2 := hπ.valF_app ⟨π x, hxV⟩ g
    simp only [AlgHom.coe_id, id_eq] at h2
    rw [h2, div_mul_cancel₀ _ hG]
  rw [key]
  exact Ideal.mul_mem_left _ _ hmem

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι), π x ∈ V.1 → x ∈ D.U i → g ∈ (D.idealSheaf.map π).ideal V → valF M₁.pt V.1 g ≠ 0 → valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x → ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  first | exact @GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | exact GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | (intros; apply GlobalTheory.Poinc.resG_f_mem_comap_map_ideal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem mem_map_idealSheaf_of_forall_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  intro o Ω _ _ _ M₁ M π hπ hprop D V g hg
  haveI : QuasiCompact π := inferInstance
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker]
  change (D.idealSheaf.subschemeι.app (π ⁻¹ᵁ V.1)).hom ((π.app V.1).hom g) = 0
  rw [GlobalTheory.Cartier.app_subschemeι_eq_zero_iff]
  intro W hW
  show _ ∈ (EffCartierData.locIdeal D.U D.f D.exists_mem D.associated_germ).ideal W
  rw [EffCartierData.mem_locIdeal_iff]
  intro i x hx hi
  have hxV : x ∈ π ⁻¹ᵁ V.1 := hW hx
  have hV : (V.1 : Set M₁.Z).Nonempty := ⟨π x, hxV⟩
  rw [GlobalTheory.Cartier.germ_resG]
  have hval : valF M.pt (π ⁻¹ᵁ V.1) ((π.app V.1).hom g) = valF M₁.pt V.1 g := hπ.valF_app hV g
  have hq := hg x hxV _ ⟨i, hi, rfl⟩
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    have hnz := GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) x hi
    have : (M.Z.presheaf.germ (D.U i) x hi).hom (D.f i) = 0 := by
      apply M.stalkHom_injective x
      rw [map_zero]
      exact (RatModel.stalkHom_germ hi (D.f i)).trans h0
    rw [this] at hnz
    exact zero_notMem_nonZeroDivisors hnz
  rw [← map_dvd_iff (M.stalkEquiv x)]
  have e1 := RatModel.stalkEquiv_germ hi (D.f i)
  have e2 := RatModel.stalkEquiv_germ hxV ((π.app V.1).hom g)
  refine ⟨⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  change (M.stalkEquiv x ((M.Z.presheaf.germ _ x hxV) ((π.app V.1).hom g)) : Ω) =
    (M.stalkEquiv x ((M.Z.presheaf.germ _ x hi) (D.f i)) : Ω) * (valF M₁.pt V.1 g / valF M.pt (D.U i) (D.f i))
  rw [e1, e2]
  simp only
  rw [hval, mul_div_cancel₀ _ hne]

end GlobalTheory.Poinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  first | exact @GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | exact GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | (intros; apply GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadRegularDivLocalEquationsProperFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.Spread

theorem isOpen_good {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (D : EffCartierData M.Z) (G : Ω) :
    IsOpen {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ : ∃ j, x ∈ D.U j := by
    have : x ∈ (⨆ i, D.U i) := D.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨(D.U j : Set M.Z) ∩ {w | G / valF M.pt (D.U j) (D.f j) ∈ M.O w}, ?_,
    (D.U j).isOpen.inter (M.isOpen_setOf_mem_O _), hj, hx _ ⟨j, hj, rfl⟩⟩
  rintro w ⟨hwj, hwG⟩ f' ⟨k, hwk, rfl⟩
  obtain ⟨u, hu⟩ := D.assoc j k
  have hne : ((D.U j ⊓ D.U k : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwj, hwk⟩
  have e1 : valF M.pt (D.U k) (D.f k) =
      valF M.pt (D.U j) (D.f j) * valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) := by
    rw [← M.valF_resG inf_le_right hne (D.f k), ← hu, ← M.res_apply _ hne, map_mul, M.res_apply, M.res_apply,
      M.valF_resG inf_le_left hne]
  have e2 : valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) *
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) = 1 := by
    rw [← M.res_apply _ hne, ← M.res_apply _ hne, ← map_mul, Units.mul_inv, map_one]
  have e3 : (valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)))⁻¹ =
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) :=
    inv_eq_of_mul_eq_one_right e2
  rw [e1, div_mul_eq_div_div, div_eq_mul_inv _ (valF M.pt (D.U j ⊓ D.U k) _), e3]
  exact mul_mem hwG (RatModel.valF_mem_O (show w ∈ D.U j ⊓ D.U k from ⟨hwj, hwk⟩) _)

end GlobalTheory.Poinc.Spread

theorem GlobalTheory.Poinc.spread_regular_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  intro o Ω _ _ _ M₁ M π _ hP D z G hG hfib
  set Good : Set M.Z := {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} with hGood
  have hcl : IsClosed (π.base '' Goodᶜ) :=
    π.isClosedMap _ (Spread.isOpen_good M D G).isClosed_compl
  have hz : z ∉ π.base '' Goodᶜ := by
    rintro ⟨x', hx', rfl⟩
    exact hx' (hfib x' rfl)
  have hW : z ∈ ({w | G ∈ M₁.O w} ∩ (π.base '' Goodᶜ)ᶜ : Set M₁.Z) := ⟨hG, hz⟩
  obtain ⟨V, hV, hzV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, (M₁.isOpen_setOf_mem_O G).inter hcl.isOpen_compl⟩) hW
  have hmem : G ∈ M₁.ringOn (V : Set M₁.Z) := RatModel.mem_ringOn.2 fun w hw => (hVW hw).1
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists ⟨z, hzV⟩).1 hmem
  refine ⟨⟨V, hV⟩, g, hzV, hg, fun x' hx' => ?_⟩
  by_contra h
  exact (hVW hx').2 ⟨x', h, rfl⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadRegularDivLocalEquationsProperFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.spread_regular_div_localEquations_proper_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  first | exact @GlobalTheory.Poinc.spread_regular_div | exact GlobalTheory.Poinc.spread_regular_div | (intros; apply GlobalTheory.Poinc.spread_regular_div <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafPullbackEqDivisorOfApprox

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc

theorem exists_idealSheaf_comap_eq_of_approx : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → (∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ x : M.Z, π x = z → IsClosed ({x} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ ∧ ∀ e : ℕ, ∃ F ∈ M₁.O z, (∀ f, EqAt M D x f → ‖M.val (gPt p ≫ y₀) F‖ = ‖M.val (gPt p ≫ y₀) f‖) ∧ ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ J : M₁.Z.IdealSheafData, J.comap π = D.idealSheaf := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU hUD hyp
  refine ⟨D.idealSheaf.map π, le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_⟩
  haveI : QuasiCompact M.s := M.qc
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  refine GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints M.Z D _ ?_
  intro x hx
  have hz : IsClosed ({π x} : Set M₁.Z) := by
    have := π.isClosedMap _ hx
    simpa [Set.image_singleton] using this
  obtain ⟨p, hp, y₀, hcen, hF⟩ := hyp (π x) hz x rfl hx
  obtain ⟨i, hi⟩ := D.exists_mem x
  have hEq : EqAt M D x (valF M.pt (D.U i) (D.f i)) := ⟨i, hi, rfl⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.generates_of_close_localEquation_classicalPoint o Ω M₁ M π hπ U D hUD x p y₀ hcen _ hEq
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_chevalley_correction_over_proper_fibre o Ω M₁ M π hπ hprop hn₁ hn U D hU hUD (π x) hz k
  obtain ⟨F, hFm, h1, h2⟩ := hF e
  obtain ⟨G, b, hFGb, hfib, hb⟩ := he ⟨F, hFm⟩ h2
  have hGf : (G : Ω) / valF M.pt (D.U i) (D.f i) ∈ M.O x := hfib x rfl _ hEq
  have hnorm : ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) (valF M.pt (D.U i) (D.f i))‖ := by
    rw [← hFGb]; exact h1 _ hEq
  obtain ⟨hG0, hfG⟩ := hk G b hnorm hb hGf
  obtain ⟨V, g, hzV, hg, hV⟩ := GlobalTheory.T.spread_regular_div_localEquations_proper_fibre o Ω M₁ M π hπ hprop D (π x) G G.2 hfib
  have hgI := GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation o Ω M₁ M π hπ hprop D V g (by rw [hg]; exact hV)
  obtain ⟨W, h, hxW, hW⟩ := GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point o Ω M₁ M π hπ D V g x i hzV hi hgI (by rw [hg]; exact hG0) (by rw [hg]; exact hfG)
  exact ⟨W, i, h, hxW, hW⟩


end GlobalTheory.Poinc
end
end
