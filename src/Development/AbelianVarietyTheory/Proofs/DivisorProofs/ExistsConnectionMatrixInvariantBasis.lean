module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftsSubEqSumInvariantFields
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerInvariantLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCobStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZe

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

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)

    simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZeStatement

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

theorem _root_.GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  first | exact @GlobalTheory.InvCoefUniq.coef_eq_zero | exact GlobalTheory.InvCoefUniq.coef_eq_zero | (intros; apply GlobalTheory.InvCoefUniq.coef_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycle

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

namespace GlobalTheory.DiffCoc

theorem rsT_rsT {Z : Scheme.{0}} {O₀ T : Z.Opens} (s : Γ(Z, O₀)) (hT : T ≤ O₀) (O : Z.Opens) (hO : O ≤ T) :
    rsT (rsT s T) O = rsT s O := by
  unfold rsT
  rw [dite_eq_left hT, dite_eq_left hO, dite_eq_left (hO.trans hT)]
  simp [resG]

theorem rsT_add {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_add (f := _)]

theorem rsT_sub {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_sub]

theorem isLift_mono {R : Type} [CommRing R] {G : Over (Sp R)} {D : R → R} {W W' : G.left.Opens} (h : W' ≤ W)
    {d : Fld G.left} (hd : IsLift G D W d) : IsLift G D W' d :=
  ⟨⟨fun O hO => hd.1.1 O (hO.trans h), fun O hO => hd.1.2.1 O (hO.trans h),
    fun O O' h' hO => hd.1.2.2 O O' h' (hO.trans h)⟩, fun O hO => hd.2 O (hO.trans h)⟩

theorem diff_isCoc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D J V d hlift hwt
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  have hl : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i := fun i i' =>
    (inf_le_left : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i)
  have hr : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i' := fun i i' =>
    (inf_le_right : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i')
  have hex : ∀ i i', ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i')), (∀ a, IsWt Y 0 _ (h a)) ∧
      ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V i') → ∀ f,
        d i O' f - d i' O' f = ∑ a, rsT (h a) O' * dd a O' f := fun i i' =>
    GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields R Dd.toPre O oa Y n v dd hdd (V i ⊓ V i') D (d i) (d i')
      (isLift_mono (hl i i') (hlift i)) (isLift_mono (hr i i') (hlift i'))
      (fun α V' hV' f hf => hwt i α V' (fun x hx => (hV' hx).1) f hf)
      (fun α V' hV' f hf => hwt i' α V' (fun x hx => (hV' hx).2) f hf)
  choose h hw hh using hex
  refine ⟨fun a i i' => h i i' a, fun a i j k => ?_, fun a i i' => hw i i' a, fun i i' W hW f => hh i i' W hW f⟩

  let U : J → Y.H.left.Opens := fun i => Y.q.left ⁻¹ᵁ V i
  let T := U i ⊓ U j ⊓ U k
  have hij : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V j) :=
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : T ≤ U i ⊓ U j)
  have hjk : T ≤ Y.q.left ⁻¹ᵁ (V j ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : T ≤ U j ⊓ U k)
  have hik : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : T ≤ U i ⊓ U k)
  let c : Fin n → Γ(Y.H.left, T) := fun b =>
    rsT (h i j b) T + rsT (h j k b) T - rsT (h i k b) T
  have hc : ∀ O, O ≤ T → ∀ f, ∑ b, rsT (c b) O * dd b O f = 0 := by
    intro O hO f
    have e : ∀ b, rsT (c b) O = rsT (h i j b) O + rsT (h j k b) O - rsT (h i k b) O := fun b => by
      simp only [c]
      rw [rsT_sub _ _ _ hO, rsT_add _ _ _ hO, rsT_rsT _ hij _ hO, rsT_rsT _ hjk _ hO, rsT_rsT _ hik _ hO]
    simp only [e, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← hh i j O (hO.trans hij) f, ← hh j k O (hO.trans hjk) f, ← hh i k O (hO.trans hik) f]
    ring
  have h0 := GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero R Y.H hsm n v dd hdd T c hc a
  simp only [c] at h0
  exact (sub_eq_zero.1 h0)

end GlobalTheory.DiffCoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycleStatement

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

theorem _root_.GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  first | exact @GlobalTheory.DiffCoc.diff_isCoc | exact GlobalTheory.DiffCoc.diff_isCoc | (intros; apply GlobalTheory.DiffCoc.diff_isCoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombinationStatement

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

theorem _root_.GlobalTheory.T.torusInvariantLift_add_invariantCombination : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  first | exact @GlobalTheory.Heat.Adjust.isLift_add_invComb | exact GlobalTheory.Heat.Adjust.isLift_add_invComb | (intros; apply GlobalTheory.Heat.Adjust.isLift_add_invComb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasis

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

namespace GlobalTheory.HeatInvLift

theorem rsT_of_le' {Z : Scheme.{0}} {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := dif_pos h

theorem rsT_rsT' {Z : Scheme.{0}} {O₀ O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Z, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le' h₁, rsT_of_le' h₂, rsT_of_le' (h₂.trans h₁), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT' {Z X : Scheme.{0}} (m : Z ⟶ X) {O₀ : X.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ m ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(X, O₀)) : rsT (pbT m s O₁) O₂ = pbT m s O₂ := by
  rw [rsT_of_le' h₂]
  unfold pbT
  rw [dif_pos h₁, dif_pos (h₂.trans h₁), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem rsT_constFn' {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) {O₀ O : Z.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn p O₀ a) O = constFn p O a := by
  rw [rsT_of_le' h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem rsT_field {Z : Scheme.{0}} {δ : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hδ : IsField ⊤ δ) {O₀ O : Z.Opens}
    (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT (δ O₀ s) O = δ O (rsT s O) := by
  rw [rsT_of_le' h, rsT_of_le' h, hδ.2.2 O₀ O h le_top s]

theorem rsT_add' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sum' {Z : Scheme.{0}} {O₀ : Z.Opens} {K : Type} (S : Finset K) (s : K → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ b ∈ S, s b) O = ∑ b ∈ S, rsT (s b) O := by
  unfold rsT; split_ifs <;> simp

end GlobalTheory.HeatInvLift

open GlobalTheory.HeatInvLift

namespace GlobalTheory.HeatInvLift

theorem exists_invLift_symmKS : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D
  obtain ⟨J, V, j, d₀, hc, hle, hl₀, hw₀⟩ := GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover R Dd O oa Y D
  obtain ⟨z, hzc, hzw, hz⟩ := GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle R Dd O oa Y n v dd hdd D J V d₀ hl₀ hw₀
  have H := fun a => GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary R Dd O oa Y n v dd hdd J V j hc hle (z a) (hzc a) (hzw a)
  choose c y hyw hy using H
  have hA := fun i => GlobalTheory.T.torusInvariantLift_add_invariantCombination R Dd O oa Y n v dd hdd D (V i) (d₀ i) (fun a => y a i) (hl₀ i) (hw₀ i) (fun a => hyw a i)
  have hrel : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f,
      (d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) - (d₀ i' W f + ∑ a, rsT (y a i') W * dd a W f) =
        ∑ a, ∑ b, constFn Y.H.hom W (Matrix.of c a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
    intro i i' W hW f
    rw [add_sub_add_comm, hz i i' W hW f]
    have hU : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
        Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i hx.1, hle i' hx.2⟩
    have key : ∀ a, rsT (z a i i') W = ∑ b, constFn Y.H.hom W (c a b) *
        dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W + (rsT (y a i') W - rsT (y a i) W) := by
      intro a
      rw [hy a i i', rsT_add', rsT_sub', rsT_rsT' inf_le_right hW, rsT_rsT' inf_le_left hW]
      congr 1
      rw [rsT_sum']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [rsT_mul', rsT_constFn' _ hW]
      congr 1
      unfold dlg
      rw [rsT_mul', rsT_field (hdd b).1 hW, rsT_pbT' _ hU hW, rsT_pbT' _ hU hW]
    simp only [key, Matrix.of_apply, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  obtain ⟨Θ, hs, hΘ⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_invariantLifts R Dd O oa Y n v dd hdd D J V j
    (fun i W f => d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) hc hle (fun i => (hA i).1) (fun i => (hA i).2)
    (Matrix.of c) hrel
  exact ⟨Θ, J, V, j, _, hs, hc, hle, fun i => (hA i).1, fun i => (hA i).2, hΘ⟩

end GlobalTheory.HeatInvLift
end
end
end
