module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensorStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDefStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodula
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicityAndRankTensorDataLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOntoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_host : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E), Nonempty (Host E) :=
  ⟨GlobalTheory.HostModel.E21, inferInstance, inferInstance, inferInstance, ⟨GlobalTheory.HostModel.host⟩⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodulaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_unitary_datum_standardLattice_tensor_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ g s : ℕ, r = s * Module.finrank ℚ E → ∃ (Dm : Datum H) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), Dm.p = s * g ∧ Dm.q = s * g ∧ (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) ∧ ∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1) := by
  first | exact @GlobalTheory.UnitaryStd.exists_datum | exact GlobalTheory.UnitaryStd.exists_datum | (intros; apply GlobalTheory.UnitaryStd.exists_datum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrix

section

@[expose] public section

open NumberField

namespace GlobalTheory

theorem finrank_dvd_of_ringOfIntegers_to_matrix (E : Type) [Field E] [NumberField E] {r : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  let g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ := (Int.castRingHom ℚ).mapMatrix.comp ρ
  let S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ) := Algebra.adjoin ℚ (Set.range g)
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    change g a * g b = g b * g a
    rw [← map_mul, mul_comm, map_mul])
  open scoped IsMulCommutative in
  letI : CommRing S := inferInstance
  let g₁ : 𝓞 E →+* S := g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  have hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y) := by
    rintro ⟨_, m, hm, rfl⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm
    have : g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ) := by
      apply Subtype.ext
      simp [g₁, g, map_intCast]
    rw [this]
    exact (IsUnit.mk0 _ hm0).map _
  let ρ' : E →+* Matrix (Fin r) (Fin r) ℚ := S.val.toRingHom.comp (IsLocalization.lift hg)
  letI : Module E (Fin r → ℚ) :=
    Module.compHom (Fin r → ℚ)
      ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')
  have hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ) := RingHom.ext_rat _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := by
    refine ⟨fun q e v => ?_⟩
    show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul]
    rfl
  refine ⟨Module.finrank E (Fin r → ℚ), ?_⟩
  have := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
  rw [Module.finrank_fin_fun] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrixStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix : ∀ (E : Type) [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  first | exact @GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | exact GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | (intros; apply GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryType

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tens_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  have hA := GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix
  have hB := GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hadj hw0 hX hr _ o hact hpsi
  obtain ⟨s, hs⟩ := hA E ρ
  obtain ⟨Dm, e, hp, hq, he, hEF⟩ := GlobalTheory.T.exists_unitary_datum_standardLattice_tensor_unimodular E H W hpos hdet ρ hadj hw0
    (D.toPre.P.g + Module.finrank ℤ D.toPre.X) s hs
  obtain ⟨hrk, hlie⟩ := GlobalTheory.T.lieMultiplicity_and_rank_tensorData_lattice R hR E H D D' W hpos hdet T ρ o hact s hs
  have hs0 : s ≠ 0 := by rintro rfl; omega
  have hX0 : 0 < Module.finrank ℤ D.toPre.X := Module.finrank_pos
  refine ⟨Dm, hp.trans hq.symm, ?_, hpsi, fun F _ _ _ => ⟨fun τ => ⟨s * D.toPre.P.g, hlie F τ, ?_⟩, fun ζ hζ hζ' => ?_⟩⟩
  · rw [hp]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hs0 (by omega))
  · rw [hrk, hp]; ring
  · obtain ⟨ev, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_compatible_symplectic_bases_levelPoints R hR D F ζ hζ hζ' _ rfl
    exact hB R hR E H D D' W hpos hdet T ρ hadj hw0 o hact hpsi Dm _ e rfl he hEF F ζ hζ hζ' ev h1 h2 h3 h4 h5
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryTypeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegData_unitary_type : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  first | exact @GlobalTheory.Mum.tens_pelOK | exact GlobalTheory.Mum.tens_pelOK | (intros; apply GlobalTheory.Mum.tens_pelOK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pelOK_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D hX
  obtain ⟨E, _, _, _, ⟨H⟩⟩ := GlobalTheory.Mum.exists_host
  obtain ⟨r, W, ρ, hr, hpos, hdet, hadj, hW⟩ := GlobalTheory.Mum.unimodLattice E H
  obtain ⟨D', ⟨T⟩⟩ := GlobalTheory.T.exists_tensorDegenerationData_of_unimodular_posDef R hR.1 D W hpos hdet
  obtain ⟨_, o, hact, hψ⟩ := GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data R hR.1 E H D D' W hpos hdet T ρ hadj hW
  obtain ⟨Dm, hDm⟩ := GlobalTheory.T.tensorDegData_unitary_type R hR E H D D' W hpos hdet T ρ hadj hW hX hr o hact hψ
  exact ⟨E, _, _, _, H, Dm, D', _, o, hDm, GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor R hR.1 D D' W hpos hdet T hr⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_unitaryPELType_factor_degData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  first | exact @GlobalTheory.Mum.exists_pelOK_factor | exact GlobalTheory.Mum.exists_pelOK_factor | (intros; apply GlobalTheory.Mum.exists_pelOK_factor <;> assumption)
end
end
