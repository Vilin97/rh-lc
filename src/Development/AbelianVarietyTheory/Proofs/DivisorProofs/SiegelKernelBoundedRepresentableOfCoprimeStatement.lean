module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObjectStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrix
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocusStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrixStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix : ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  first | (exact @GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (exact GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (intros; apply GlobalTheory.ZarhinFam.exists_spanning_family_posDef  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilled

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d hh hM hMo hd hcop
  obtain ⟨r, eO, W, d₀, hspan, hW, hd₀, hid⟩ := GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix d hd
  obtain ⟨jl, n, o, κ, hex⟩ := GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy h M d hh hM hMo hd hcop
  exact ⟨GlobalTheory.ZarhinFam.ord d, inferInstance, GlobalTheory.ZarhinFam.bar d, r, eO, W, d₀, GlobalTheory.ZarhinFam.idem d, jl, n, o, κ,
    GlobalTheory.ZarhinFam.bar_add d, hspan, hW, hd₀, hid, GlobalTheory.ZarhinFam.idem_mul_self d, hex,
    fun S t c z₁ z₂ act₁ act₂ => GlobalTheory.T.zarhinTrick_principal_objects_iso_unique h M d hh hM hMo hd hcop jl n o κ S t c z₁ z₂ act₁ act₂⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilledStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (exact GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (intros; apply GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprime

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem sdRep_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  intro h M d hh hM hodd hd hcop
  obtain ⟨O, _, bar, r, eO, W, d₀, e, jl, n, o, κ, hbar, hspan, hW, hd₀, hsum, hee, hex, huniq⟩ :=
    GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled h M d hh hM hodd hd hcop
  obtain ⟨H, sH, zH, actH, hpr, hra, hadj, hq, hln, hrep⟩ :=
    GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction (8 * h) M (by omega) hM hodd O bar r eO W d₀ hbar hspan hW hd₀ hsum
  obtain ⟨Y, j, c, hj, hjq, hker, hunit, hpull, huniv⟩ :=
    GlobalTheory.T.siegel_family_idempotent_image_open_locus h (8 * h) M d O bar e jl n o κ H sH zH actH hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨Y, j ≫ sH, c, hker, hunit, isQProjOver_comp_immersion j sH hj hjq hq, ?_⟩
  intro S t c' hdu hc'
  obtain ⟨z', act', hz'p, hz'r, hz'a, hz'rel⟩ := hex S t c' hdu hc'
  obtain ⟨g, ⟨hg, hgpb⟩, -⟩ := hrep S t z' act' hz'p hz'r hz'a
  obtain ⟨y, ⟨hy, hyc⟩, -⟩ := huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hg], hyc⟩, ?_⟩
  rintro f ⟨hf, hfc⟩
  obtain ⟨w, actw, hwp, hwr, hwa, hwpb, hwrel⟩ := hpull S t f c' hf hfc
  have hiso := huniq S t c' w z' actw act' hdu hc' hwp hz'p hwr hz'r hwa hz'a hwrel hz'rel
  have h2 : ActPB w actw zH actH (𝟙 S ≫ g) := hiso.trans hgpb
  rw [Category.id_comp] at h2
  have hfj : f ≫ j = g :=
    (hrep S t w actw hwp hwr hwa).unique ⟨by rw [Category.assoc]; exact hf, hwpb⟩ ⟨hg, h2⟩
  exact (huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩).unique ⟨hfj, hfc⟩ ⟨hy, hyc⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  first | (exact @GlobalTheory.UPel.HT.sdRep_of_coprime) | (exact GlobalTheory.UPel.HT.sdRep_of_coprime) | (intros; apply GlobalTheory.UPel.HT.sdRep_of_coprime  <;> assumption)
end
end
