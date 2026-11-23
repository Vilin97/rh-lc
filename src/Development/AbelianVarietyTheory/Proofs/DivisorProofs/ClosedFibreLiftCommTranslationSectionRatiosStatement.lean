module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreRemIndep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCarriesRatioDatumRemainderStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivSec

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

theorem exists_div_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s a b : LB.Sec (LB.LinComb L φ ε)) (U : Y.Opens) (f : Γ(Y, U))
    (hs : ∀ z ∈ U, ∀ J, Good L z J → IsUnit (sval s (𝟙 Y) z J)) :
    ∃ g : Γ(Y, U), ∀ z ∈ U, ∀ J, Good L z J →
      sval a (𝟙 Y) z J = gs (𝟙 Y) z U f * sval b (𝟙 Y) z J + gs (𝟙 Y) z U g * sval s (𝟙 Y) z J := by
  have hun : ∀ (j : K → L.ι) (y : Y), y ∈ U → y ∈ LB.wchart L φ j →
      IsUnit (gs (𝟙 Y) y (LB.wchart L φ j) (s.f j)) := fun j y hU hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [e]
    exact (Units.isUnit _).mul (hs y hU J hJ)
  let W : (K → L.ι) → Y.Opens := fun j => U ⊓ LB.wchart L φ j
  have hloc : ∀ j, ∃ u : Γ(Y, W j), ∀ y ∈ W j,
      gs (𝟙 Y) y (LB.wchart L φ j) (a.f j) = gs (𝟙 Y) y U f * gs (𝟙 Y) y (LB.wchart L φ j) (b.f j) +
        gs (𝟙 Y) y (W j) u * gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) := by
    intro j
    have l₁ : W j ≤ U := inf_le_left
    have l₂ : W j ≤ LB.wchart L φ j := inf_le_right
    have hu : IsUnit ((Y.presheaf.map (homOfLE l₂).op).hom (s.f j)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 Y) y (W j) hy _).symm.trans (gs_res (𝟙 Y) y l₂ hy (s.f j)))).mpr
          (hun j y hy.1 hy.2)
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have key : (Y.presheaf.map (homOfLE l₂).op).hom (a.f j) =
        (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j) +
        (((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v) *
          (Y.presheaf.map (homOfLE l₂).op).hom (s.f j) := by
      rw [_root_.mul_assoc, hv]; ring
    refine ⟨((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v, fun y hy => ?_⟩
    refine (gs_res (𝟙 Y) y l₂ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (W j)) key).trans ?_)
    refine (gs_add (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y l₁ hy _) (gs_res (𝟙 Y) y l₂ hy _))
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg _ (gs_res (𝟙 Y) y l₂ hy _))
  choose u hu using hloc
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' W U (fun j => homOfLE inf_le_left) (fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => I (φ k), hy, Set.mem_iInter.2 fun k => hI _⟩) u
    (fun j j' => fn_ext (V := W j ⊓ W j') fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      have e₁ := hu j y hy.1
      have e₂ := hu j' y hy.2
      rw [sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, sec_trans b (𝟙 Y) y hy.1.2 hy.2.2,
        sec_trans s (𝟙 Y) y hy.1.2 hy.2.2] at e₁
      have hc := (Units.isUnit (trF φ ε (𝟙 Y) y j j')).mul (hun j' y hy.1.1 hy.2.2)
      refine hc.mul_right_cancel ?_
      linear_combination (trF φ ε (𝟙 Y) y j j').val * e₂ - e₁)
  refine ⟨g, fun z hz J hJ => ?_⟩
  have hm : z ∈ W (fun k => J (𝟙 Y ≫ φ k)) := ⟨hz, hJ.mem φ (𝟙 Y)⟩
  have e : gs (𝟙 Y) z U g = gs (𝟙 Y) z (W _) (u (fun k => J (𝟙 Y ≫ φ k))) :=
    (gs_res (𝟙 Y) z inf_le_left hm g).symm.trans (congrArg (gs (𝟙 Y) z (W _)) (hg _))
  rw [e]
  exact hu _ z hm

theorem exists_isRem : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (α : Q.X) (σ σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ g : Γ(Q.P.A.left, U), GlobalTheory.HeatRatio.IsRem Q σ' σp σp' U f g := by
  intro R _ _ Q N α σ σ' σp σp' U f h
  exact exists_div_sec Q.P.isLB σ' σp σp' U f fun z hz J hJ => (h z hz J hJ).1

end GlobalTheory.HeatRatio
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatioTwoMul

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatRatio.Square

variable {R : Type} [CommRing R] [IsDomain R]

theorem famφB_zero_one (Q : DegPre R) : Q.famφB 0 1 = 𝟙 _ := by
  show (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c 0)).left = 𝟙 _
  rw [GlobalTheory.Mum.degPre_c_zero, padd, comp_one, ← Hom.mul_def, _root_.mul_one]
  rfl

theorem famφB_zero_two (Q : DegPre R) : Q.famφB 0 2 = Q.famφB 0 3 := by
  show (toUnit Q.P.A ≫ Q.c 0).left = (toUnit Q.P.A ≫ η[Q.P.A]).left
  rw [GlobalTheory.Mum.degPre_c_zero, comp_one, Hom.one_def]

theorem formEq (Q : DegPre R) (N : ℕ) :
    FormEq (Sum.elim (Q.famφB 0) (Q.famφB 0)) (Sum.elim (DegPre.famε N) (DegPre.famε N))
      (Q.famφB 0) (DegPre.famε (2 * N)) := by
  intro U _ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four]
  have e1 := famφB_zero_one Q
  have e2 := famφB_zero_two Q
  have e0 : Q.famφB 0 0 = 𝟙 _ := rfl
  rw [e1, e2, e0]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize h (𝟙 _) = a
  generalize h (Q.famφB 0 3) = b
  push_cast
  have hs : ∀ k : ℤ, a ^ (k - 1) * a ^ (1 : ℤ) = a ^ k := fun k => by rw [← zpow_add, sub_add_cancel]
  rw [hs, hs, zpow_neg_one, zpow_one, inv_mul_cancel_right, inv_mul_cancel_right, ← zpow_add, two_mul]

theorem isRatio_two_mul (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens)
    (f : Γ(Q.P.A.left, U)) (_hN : 1 ≤ N) (h : GlobalTheory.HeatRatio.IsRatio Q σ σ' U f) :
    ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f := by
  obtain ⟨ρ, hρ⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ σ')
  obtain ⟨ρ', hρ'⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ' σ')
  refine ⟨ρ, ρ', fun z hz J hJ => ?_⟩
  obtain ⟨hu, he⟩ := h z hz J hJ
  rw [hρ _ _ z J hJ, hρ' _ _ z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, he]
  exact ⟨hu.mul hu, by ring⟩

end GlobalTheory.HeatRatio.Square

theorem GlobalTheory.HeatRatio.isRatio_square : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), 1 ≤ N → GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f :=
  fun _ _ _ Q N σ σ' U f hN h => GlobalTheory.HeatRatio.Square.isRatio_two_mul Q N σ σ' U f hN h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatios

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.HeatRatioW.exists_acts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ



theorem GlobalTheory.HeatRatioW.dl_comm_transl_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc y T₀ hT₀ hT₀' N hN σ σ' U f hf
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hr : GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f := hf
  have hN2 : 1 ≤ 2 * N := by omega
  obtain ⟨ρ₁, ρ₁', hr2⟩ := GlobalTheory.HeatRatio.isRatio_square _ P.D.toPre N σ σ' U f hN hr
  have HA := fun (k' : ℕ) (α : P.D.toPre.X) (s : P.D.toPre.SecB k' α) =>
    GlobalTheory.HeatRatioW.exists_acts P.D Y v' dd hdd _ D h hb k' α s
  obtain ⟨σp, a1⟩ := HA N 0 σ
  obtain ⟨σp', a2⟩ := HA N 0 σ'
  obtain ⟨ρp, a3⟩ := HA (2 * N) 0 ρ₁
  obtain ⟨ρp', a4⟩ := HA (2 * N) 0 ρ₁'
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre N 0 σ σ' σp σp' U f hr
  obtain ⟨g₂, hg₂⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre (2 * N) 0 ρ₁ ρ₁' ρp ρp' U f hr2
  have e1 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 0 0 σ σ' σp σp' ρ₁ ρ₁' ρp ρp' U f g₁ g₂ hr hr2 a1 a2 a3 a4 hg₁ hg₂
  obtain ⟨β₁, s, s', sp, sp', b1, b2, b3, b4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y N hN σ σ' σp σp' U f g₁ hr a1 a2 hg₁
  obtain ⟨β₂, r, r', rp, rp', c1, c2, c3, c4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y (2 * N) hN2 ρ₁ ρ₁' ρp ρp' U f g₂ hr2 a3 a4 hg₂
  have e2 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 β₁ β₂ s s' sp sp' r r' rp rp' _ _ _ _ b1 c1 b2 b3 c2 c3 b4 c4

  set T := (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left with hTdef
  have hle : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ T₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := by
    intro x hx
    have e : (T₀ ≫ m₀) x = (m₀ ≫ T) x := by rw [hT₀]
    show m₀ (T₀ x) ∈ U
    have e' : m₀ (T₀ x) = T (m₀ x) := by simpa using e
    rw [e']; exact hx
  have key : ∀ (φ ψ : A₀.left ⟶ P.D.toPre.P.A.left), φ = ψ → ∀ (h1 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ U)
      (h2 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ ψ ⁻¹ᵁ U), φ.appLE U _ h1 = ψ.appLE U _ h2 := by
    rintro φ _ rfl _ _; rfl
  have L5 : ∀ g : Γ(P.D.toPre.P.A.left, U), (m₀.app (T ⁻¹ᵁ U)).hom ((T.app U).hom g) =
      (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom ((m₀.app U).hom g) := by
    intro g
    have c1 := Scheme.Hom.comp_appLE m₀ T U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_rfl
    have c2 := Scheme.Hom.comp_appLE T₀ m₀ U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) (le_trans hle le_rfl)
    have c3 := key _ _ hT₀ (le_trans hle le_rfl) le_rfl
    have := congrArg (fun φ => φ.hom g) (c2.symm.trans (c3.trans c1))
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  rw [pbT, dite_eq_left hle]
  set φ := (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom
  rw [L5, L5] at e2
  have h1 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - (m₀.app U).hom g₁ := by
    push_cast at e1; linear_combination e1
  have h2 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) * dl _ ((T.app U).hom f) =
      φ ((m₀.app U).hom g₂) - φ ((m₀.app U).hom g₁) := by
    push_cast at e2; linear_combination e2
  rw [← map_sub, ← h1, map_mul, map_mul, map_ofNat, map_natCast] at h2
  have hu : IsUnit (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) := by
    let ψ : k →+* Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) :=
      (A₀.hom.appLE ⊤ (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have hk : IsUnit (2 * N : k) := by
      refine IsUnit.mk0 _ ?_
      exact_mod_cast (by omega : 2 * N ≠ 0)
    have := hk.map ψ
    rwa [map_mul, map_ofNat, map_natCast] at this
  exact hu.mul_left_cancel h2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatiosStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closedFibreLift_comm_translation_section_ratios : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  first | exact @GlobalTheory.HeatRatioW.dl_comm_transl_ratio | exact GlobalTheory.HeatRatioW.dl_comm_transl_ratio | (intros; apply GlobalTheory.HeatRatioW.dl_comm_transl_ratio <;> assumption)
end
end
