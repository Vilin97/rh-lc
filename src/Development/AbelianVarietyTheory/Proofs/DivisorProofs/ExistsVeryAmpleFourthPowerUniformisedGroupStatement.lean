module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIsoStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

theorem sections_move_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  intro R _ _ I D A G _ _ U k m hk b
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw', -⟩ := GlobalTheory.Algebraise.exists_swap _ _ w hw (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  choose s hs using fun i => GlobalTheory.Algebraise.exists_down A.isLB U.LG.isLB U.gen.hom.left
    (pullback.fst G.hom (jK R)) w' hw' (b i)
  choose c' σ hc' hσ using fun i => GlobalTheory.FormalGeneric.exists_integral U hk (s i)
  refine ⟨σ, fun i => Units.mk0 (algebraMap R (FractionRing R) (c' i))
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hc' i)), fun y j jA hj hjA => ?_⟩
  refine ⟨(gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k)⁻¹, fun i => ?_⟩
  have e₁ := hs i _ (𝟙 _) y (jA 0) (j 0) hjA hj
  have e₂ := hσ i _ (𝟙 _) y (j 0) hj
  have hc : cst (pullback.snd G.hom (jK R) ≫ jK R) y (c' i) = gs (pullback.snd G.hom (jK R)) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (c' i))) :=
    (gs_pull _ (jK R) y ⊤ trivial _).symm.trans
      (congrArg (gs _ y ⊤) (GlobalTheory.FormalGeneric.appTop_spec (algebraMap R (FractionRing R)) (c' i)))
  rw [Category.id_comp] at e₁ e₂
  rw [Category.id_comp, hc] at e₂
  rw [GlobalTheory.Algebraise.fin_one_const j, GlobalTheory.Algebraise.fin_one_const jA]
  change GlobalTheory.SectionRingIso.vl (σ i) _ y _ = _ * _ * GlobalTheory.SectionRingIso.vl (b i) _ y _
  rw [e₂, e₁, Units.val_mk0, ← Units.val_pow_eq_pow_val]
  generalize gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k = v
  rw [_root_.mul_assoc, mul_left_comm _ v.val, Units.inv_mul_cancel_left]
  rfl

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_integral_sections_uniformisedGroup_power : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  first | exact @GlobalTheory.Mum.sections_move_integral | exact GlobalTheory.Mum.sections_move_integral | (intros; apply GlobalTheory.Mum.sections_move_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FieldVA

variable {X : Scheme.{0}}

theorem nonzeroLocus_pullPow (L : LB X) (N : ℕ) (t : (lbPow L N).Sec) :
    nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 X) t) = nonzeroLocus t := by
  apply le_antisymm
  · refine iSup_le fun j y hy => ?_
    have hy' : y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _ (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) j)).hom
        (t.f (fun _ => j 0))) := hy
    rw [Scheme.basicOpen_appLE] at hy'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hy'.2⟩
  · refine iSup_le fun j y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j PUnit.unit, ?_⟩
    have hc : y ∈ (lbPow L N).U j := X.basicOpen_le (t.f j) hy
    show y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _
      (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) (fun _ => j PUnit.unit))).hom (t.f (fun _ => j PUnit.unit)))
    rw [Scheme.basicOpen_appLE]
    exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc PUnit.unit, hy⟩

end GlobalTheory.Mum.FieldVA

namespace GlobalTheory.Mum


open GlobalTheory.Mum.FieldVA in
theorem veryAmpleAlong_field (hA : AmpleSt) (K : Type) [Field K] (P : PolAV (Sp K)) :
    ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  obtain ⟨m, t, hcov, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow hA K P 4 le_rfl
  have hb : ∀ i, nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) :=
    fun i => nonzeroLocus_pullPow P.L 4 (t i)
  refine ⟨m, fun i => GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i), ?_, fun i => ?_⟩
  · refine _root_.top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i ∈ Set.univ, nonzeroLocus (t i) by rw [hcov]; trivial)
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, show y ∈ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) by
      rw [hb]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i (Set.mem_univ i)
  have hW : (𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) := by
    rw [← hb i]; exact le_antisymm (fun y hy => hy) (fun y hy => hy)
  have le1 := hW.le
  have le2 := hW.ge
  have hconst : ∀ a, resG P.A.left le1 (constFn P.A.hom (nonzeroLocus (t i)) a) =
      AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := by
    intro a
    have h2 : constFn P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a =
        AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := rfl
    refine (fn_ext fun x hx => ?_).trans h2
    rw [gs_res _ x le1 hx, gs_constFn _ _ _ _ (le1 hx), gs_constFn _ _ _ _ hx]
  refine ⟨by rw [hW]; exact haff, fun j => resG P.A.left le1 (r j), fun j c a ha hc => ?_, ?_⟩
  · have hc' : a ∈ (lbPow P.L 4).U (fun _ => c 0) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc 0
    have key : ∀ s : (lbPow P.L 4).Sec, secGerm (𝟙 P.A.left) a (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) s) c =
        gs (𝟙 P.A.left) a ((lbPow P.L 4).U (fun _ => c 0)) (s.f (fun _ => c 0)) := fun s =>
      (gs_appLE (𝟙 P.A.left) _ _ _ (𝟙 P.A.left) a hc _).trans
        (congrArg (fun q => gs q a _ (s.f (fun _ => c 0))) (Category.id_comp _))
    have hm : (𝟙 P.A.left) a ∈ nonzeroLocus (t i) ⊓ (lbPow P.L 4).U (fun _ => c 0) := ⟨le1 ha, hc'⟩
    have e := congrArg (gs (𝟙 P.A.left) a _) (hr j (fun _ => c 0))
    rw [gs_res _ a _ hm, gs_mul _ a _ hm, gs_res _ a _ hm, gs_res _ a _ hm] at e
    rw [key, key, gs_res _ a le1 ha]
    exact e
  · have hρ : ∀ f, resG P.A.left le1 (resG P.A.left le2 f) = f := fun f => fn_ext fun x hx => by
      rw [gs_res _ x le1 hx, gs_res _ x le2 (le1 hx)]
    have hcl : Subring.closure (Set.range (constFn P.A.hom (nonzeroLocus (t i))) ∪ Set.range r) ≤
        (MvPolynomial.eval₂Hom (AbLaw.cst P.A.hom
          ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))))
          (fun j => resG P.A.left le1 (r j))).range.comap (resG P.A.left le1) := by
      refine Subring.closure_le.2 ?_
      rintro g (⟨a, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.C a, by
          rw [MvPolynomial.eval₂Hom_C]; exact (hconst a).symm⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.X j, by rw [MvPolynomial.eval₂Hom_X']⟩)
    intro f
    obtain ⟨p, hp⟩ := RingHom.mem_range.1 (Subring.mem_comap.1
      (hcl (hsurj ▸ Subring.mem_top (resG P.A.left le2 f))))
    exact ⟨p, hp.trans (hρ f)⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field : AmpleSt → ∀ (K : Type) [Field K] (P : PolAV (Sp K)), ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_field | exact GlobalTheory.Mum.veryAmpleAlong_field | (intros; apply GlobalTheory.Mum.veryAmpleAlong_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_veryAmpleAlong_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  intro R _ _ I D A G _ _ U
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field GlobalTheory.lawsAndExpansions.1.1.ample _ A
  obtain ⟨σ, c, H⟩ := GlobalTheory.T.exists_integral_sections_uniformisedGroup_power R I D A G U (k := 4) (by norm_num) b
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact ⟨m, σ, GlobalTheory.T.veryAmpleAlongPullback_transport_iso _ A.A.hom U.gen.hom.left (Over.w U.gen.hom) _ U.LG.isLB A.isLB b hb σ c H⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  first | exact @GlobalTheory.Mum.exists_veryAmpleAlong_unif | exact GlobalTheory.Mum.exists_veryAmpleAlong_unif | (intros; apply GlobalTheory.Mum.exists_veryAmpleAlong_unif <;> assumption)
end
end
