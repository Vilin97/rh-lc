module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodularStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTupleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTensorTorsionEqProdComponentsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.MumValues

theorem exists_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  intro R _ _ _ hR D F _ _ _
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.allSixLaws.1 R D.toPre D.psi_even D.tau_bimult F ⊤
    (fun _ => trivial)
  exact ⟨N, ⟨ν⟩⟩

end GlobalTheory.MumValues
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_degenerationValues_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  first | exact @GlobalTheory.MumValues.exists_values | exact GlobalTheory.MumValues.exists_values | (intros; apply GlobalTheory.MumValues.exists_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTuple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_pow {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (h : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by
      have := h.2.2.1 0 0 j
      rw [add_zero] at this
      exact (add_eq_left.1 this.symm)
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem exists_ptRel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k ps
  have B := GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have B' := GlobalTheory.Ex.GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hT := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  choose qs hqs using fun i => ((B.2.2.2.2 k).1 (ps i)).exists
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT fun j => (qs j).1.2
  obtain ⟨y', hy'⟩ := hT.2.2.2.1.2 fun i => (qs i).1.1.toAdd
  have hk : v' ^ k = N'.io y' := by
    refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT _ _ (fun j => N.io (chi T ν ν' y' j))
      ?_ (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT y')
    have hp := gtRelV_pow hT hv' k
    have e : ((fun j => (qs j).1.2) ^ k : Fin r → N.Gt) = fun j => N.io (chi T ν ν' y' j) := by
      funext j
      rw [Pi.pow_apply, hy']
      exact (qs j).2
    rwa [e] at hp
  let q' : N'.QT k := ⟨(Multiplicative.ofAdd y', v'), hk⟩
  obtain ⟨p', hp'⟩ := (B'.2.2.2.2 k).2.1 q'
  exact ⟨p', q', qs, hp', hqs, fun i => congrFun hy' i, hv'⟩

end GlobalTheory.Mum.TensTor
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTupleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_tensor_torsion_point_of_component_tuple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  first | exact @GlobalTheory.Mum.TensTor.exists_ptRel | exact GlobalTheory.Mum.TensTor.exists_ptRel | (intros; apply GlobalTheory.Mum.TensTor.exists_ptRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrixStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  first | exact @GlobalTheory.Mum.TensAct.qkAct_tens | exact GlobalTheory.Mum.TensAct.qkAct_tens | (intros; apply GlobalTheory.Mum.TensAct.qkAct_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOnto

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

theorem GlobalTheory.Mum.TensTor.zpow_sum_tens {M κ : Type} [CommGroup M] (a : M) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem GlobalTheory.Mum.TensTor.tate_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ hdet T ρ hρ _ _ o hact _ Dm g e _ he hEF F _ _ _ ζ hprim hpow ev hadd hker
    honto htow hweil

  obtain ⟨N, ⟨ν⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D F
  obtain ⟨N', ⟨ν'⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D' F
  choose P hP using fun (n : ℕ) (a : Dm.La) =>
    GlobalTheory.T.exists_tensor_torsion_point_of_component_tuple R hB D D' W T F N N' ν ν' n (fun j => ev n (e a j))
  refine ⟨⟨ζ, hprim, hpow, P, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  ·
    intro n hn a b
    have hs := hP n (a + b)
    simp only [map_add (f := _), Pi.add_apply] at hs
    exact GlobalTheory.T.tensor_torsion_add_componentwise R hB D D' W T F N N' ν ν' n (P n a) (P n b) (P n (a + b)) _ _ _ (hP n a) (hP n b) hs
      (fun i => hadd n hn (e a i) (e b i))
  ·
    intro n hn x a
    have hs := hP n (x • a)
    simp only [he] at hs
    exact GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix R hB D D' W T F N N' ν ν' E H ρ hρ o hact g ev hadd hker n hn x (fun j => e a j)
      (P n a) (P n (x • a)) (hP n a) hs
  ·
    intro n hn a b
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n a) (P n b) _ _ (hP n a) (hP n b)]
    simp only [hker n hn]
    constructor
    · intro h
      choose c hc using h
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_add (f := _), map_nsmul, e.apply_symm_apply]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, hc i]
    · rintro ⟨c, rfl⟩ i
      exact ⟨e c i, by simp only [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply]⟩
  ·
    intro n hn p
    obtain ⟨ps, hps⟩ := GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular R hB D D' W T F N N' ν ν' hdet n p
    choose a ha using fun i => honto n hn (ps i)
    refine ⟨e.symm a, ?_⟩
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n (e.symm a)) p _ ps (hP n (e.symm a)) hps]
    intro i
    simpa only [e.apply_symm_apply] using ha i
  ·
    intro n m hn hm a
    exact GlobalTheory.T.tensor_torsion_tower_nsmul_componentwise R hB D D' W T F N N' ν ν' n m hn hm (P (n * m) a) _ (P n a) _ (hP (n * m) a) (hP n a)
      (fun i => htow n m hn hm (e a i))
  ·

    intro n hn a b
    have h := GlobalTheory.T.weil_pairing_tensor_torsion_eq_prod_components R hB D D' W T F N N' ν ν' n hn (P n a) (P n b) _ _ (hP n a) (hP n b)
      (fun i j => ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) (fun i j => hweil n hn (e a i) (e b j))
    have key : (∏ i, ∏ j, (ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) ^ (W + W.transpose) i j) =
        ζ n ^ Dm.EF a b := by
      rw [hEF a b, zpow_sum_tens]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_sum_tens]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul, mul_comm ((W + W.transpose) i j)]
    beta_reduce at h
    rwa [key] at h
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOntoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  first | exact @GlobalTheory.Mum.TensTor.tate_tens | exact GlobalTheory.Mum.TensTor.tate_tens | (intros; apply GlobalTheory.Mum.TensTor.tate_tens <;> assumption)
end
end
