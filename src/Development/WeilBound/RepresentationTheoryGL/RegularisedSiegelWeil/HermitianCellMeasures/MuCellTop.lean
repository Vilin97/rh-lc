module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFormulaOfInvM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDivRp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteBadScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixEqBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingHomMulSubEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianFields

section

@[expose] public section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.UnitCell

theorem artinian_fields {ι : Type} [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, IsArtinianRing (A i)]
    {R : Type} [CommRing R] (c : ∀ i, R →+* A i) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ k, Field (Ω k)) (φ : ∀ k, R →+* Ω k),
      (∀ x, (∀ i, c i x = 1) → ∀ k, φ k x = 1) ∧
      ∀ z, (∀ k, φ k z ≠ 0) ↔ ∀ i, IsUnit (c i z) := by
  obtain ⟨m, ⟨q⟩⟩ := Finite.exists_equiv_fin (Σ i, MaximalSpectrum (A i))
  have hmax : ∀ k : Fin m, (q.symm k).2.asIdeal.IsMaximal := fun k => (q.symm k).2.isMaximal
  refine ⟨m, fun k => A (q.symm k).1 ⧸ (q.symm k).2.asIdeal, fun k => Ideal.Quotient.field _,
    fun k => (Ideal.Quotient.mk _).comp (c (q.symm k).1), fun x hx k => ?_, fun z => ⟨fun hz i => ?_, fun hz k h => ?_⟩⟩
  · simp [hx]
  · by_contra hu
    obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits hu
    obtain ⟨k, hk⟩ : ∃ k, q.symm k = ⟨i, ⟨M, hM⟩⟩ := ⟨q _, q.symm_apply_apply _⟩
    refine hz k (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hk]
    exact hzM
  · have hk := hmax k
    have h' : c (q.symm k).1 z ∈ (q.symm k).2.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
    exact hk.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hz _))

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sc {R : Type} [CommRing R] (r : Rˣ) : GL (Fin 1) R := Units.map (Matrix.scalar (Fin 1)).toMonoidHom r

theorem sc_apply {R : Type} [CommRing R] (r : Rˣ) : (sc r).1 0 0 = r := by simp [sc]

theorem exists_adele (S : Finset (HeightOneSpectrum (𝓞 F))) (b : ∀ v : HeightOneSpectrum (𝓞 F), (Fv F v ⊗[F] E)ˣ)
    (hb : ∀ v ∉ S, b v = 1) (c : ∀ w : InfinitePlace F, (w.Completion ⊗[F] E)ˣ) :
    ∃ x : AF F ⊗[F] E, (∀ v, compFin F E v x = b v) ∧ ∀ w, compInf F E w x = c w := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components S (fun v => sc (b v))
    (fun v hv => by rw [hb v hv]; exact map_one _) (fun w => sc (c w))
  refine ⟨a.1 0 0, fun v => ?_, fun w => ?_⟩
  · have h := congrArg (fun g : GL (Fin 1) (Fv F v ⊗[F] E) => g.1 0 0) (ha v)
    exact h.trans (sc_apply _)
  · have h := congrArg (fun g : GL (Fin 1) (w.Completion ⊗[F] E) => g.1 0 0) (hc w)
    exact h.trans (sc_apply _)


variable (F E) in
def LocR (S : Finset (HeightOneSpectrum (𝓞 F))) : InfinitePlace F ⊕ S → Type
  | .inl w => w.Completion ⊗[F] E
  | .inr v => Fv F v.1 ⊗[F] E

instance locRing (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, CommRing (LocR F E S c)
  | .inl w => inferInstanceAs (CommRing (w.Completion ⊗[F] E))
  | .inr v => inferInstanceAs (CommRing (Fv F v.1 ⊗[F] E))


variable (F E) in
def locC (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, AF F ⊗[F] E →+* LocR F E S c
  | .inl w => compInf F E w
  | .inr v => compFin F E v.1

instance locArt (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, IsArtinianRing (LocR F E S c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rintro (w | v)
  · exact IsArtinianRing.of_finite w.Completion (w.Completion ⊗[F] E)
  · exact IsArtinianRing.of_finite (Fv F v.1) (Fv F v.1 ⊗[F] E)


open Classical in
theorem crit (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E) (h1 : ∀ w, compInf F E w e = 1)
    (h2 : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ i, Field (Ω i)) (φ : ∀ i, AF F ⊗[F] E →+* Ω i), (∀ i, φ i e = 1) ∧
      ∀ z : AF F ⊗[F] E, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0 := by
  obtain ⟨m, Ω, fld, φ, hφ, hu⟩ := artinian_fields (LocR F E S) (locC F E S)
  have he : ∀ k, φ k e = 1 := hφ e (by
    rintro (w | ⟨v, hv⟩)
    · exact h1 w
    · exact (h2 v).trans (if_pos hv))
  refine ⟨m, Ω, fld, φ, he, fun z => ⟨fun h k => ?_, fun h => ?_⟩⟩
  · have h' := h.map (φ k)
    rw [map_add (f := _), map_sub, map_mul, map_one, he, sub_self, zero_add, one_mul] at h'
    exact h'.ne_zero
  · have hz := (hu z).1 h
    have hI : ∀ w, IsUnit (compInf F E w z) := fun w => hz (.inl w)
    have hS : ∀ v (h : v ∈ S), IsUnit (compFin F E v z) := fun v h => hz (.inr ⟨v, h⟩)
    obtain ⟨x, hxf, hxi⟩ := exists_adele (E := E) S
      (fun v => if h : v ∈ S then (hS v h).unit⁻¹ else 1) (fun v hv => dif_neg hv) (fun w => (hI w).unit⁻¹)
    refine isUnit_iff_exists_inv.2 ⟨x, GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) fun v => ?_⟩
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h1, hxi, sub_self, zero_add, one_mul]
      exact (hI w).mul_val_inv
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h2, hxf]
      by_cases hv : v ∈ S
      · simp only [if_pos hv, dif_pos hv, sub_self, zero_add, one_mul]
        exact (hS v hv).mul_val_inv
      · simp [if_neg hv, dif_neg hv]

end Glue

theorem unitCrit : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.UnitCrit := fun _ D S e he =>
  crit S e he.1 (by convert he.2 using 4)

end GlobalTheory.CompanionTheory.UnitCell

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswTop

theorem topC : PositivityTheory.Rg.Rsw.Cell.TopC := by
  intro D p e
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D p e
  exact ⟨inferInstance, inferInstance, inferInstance, h2, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.RswTop
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellOf

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Cell

theorem muCell_of (hR : Riesz) (hN : NullC) (hF : CellFormula) (hA : CellAlg) (hD : Decomp) (hW : FewC) (hS : SetC)
    (hT : TopC) : MuCell := by
  intro D p mu hmu nb hnb w hw
  refine ⟨∅, fun S _ e he lam hlam => ?_⟩
  obtain ⟨hG2, hGlc, hGsc, hH2, hHlc, hHsc, hHb⟩ := hT D p e
  haveI := hlam
  obtain ⟨h, hSet, hRho, hKh, hInv⟩ := hS D p mu hmu
  letI : MeasurableSpace (G D p ⧸ P D p) := borel _
  haveI : BorelSpace (G D p ⧸ P D p) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := hR (G D p) (P D p) h mu hSet
  obtain ⟨τ, hcell, -, hmm⟩ := hA D p nb hnb w hw S e he
  have hfew : Few (P D p) h mu (cell e) :=
    hW D p mu h nb hnb w hw (fun y => (hInv nb hnb w hw y).2) S e he
  have hnull : ν {q | rp q ∉ cell e} = 0 :=
    hN (G D p) (P D p) h mu hSet ν hν (cell e) hcell.isOpen
      (fun q hq x hx => (hcell.left q hq x hx).1) hfew
  have hdec : ∀ x ∈ cell e, ∃ q ∈ P D p, ∃ u ∈ KOff D p S, x = q * (w * nb (τ x).1) * u ∧
      ∀ z : hermS D p e, nb z.1 * u = u * nb z.1 :=
    fun x hx => hD D p nb hnb w hw S e he x hx (τ x) (hmm x hx)
  have hrel : ∀ (y : hermS D p e), ∀ x ∈ cell e,
      h (x * nb y.1) * h (w * nb (τ x).1) = h (w * nb (τ x + y).1) * h x := by
    intro y x hx
    obtain ⟨q, hq, u, hu, ex, hcomm⟩ := hdec x hx
    have hadd : nb (τ x + y).1 = nb (τ x).1 * nb y.1 := hcell.nbAdd (τ x) y
    have e0 : h (x * nb y.1) = h (q * (w * nb (τ x).1) * u * nb y.1) :=
      congrArg (fun z => h (z * nb y.1)) ex
    have e1 : q * (w * nb (τ x).1) * u * nb y.1 = q * (w * nb (τ x + y).1) * u := by
      rw [hadd]
      simp only [mul_assoc]
      rw [← hcomm y]
    have hx1 : h (x * nb y.1) = h (q * (w * nb (τ x + y).1)) := by
      rw [e0, e1, hKh S u hu]
    have hx2 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    rw [hx1, hx2]
    exact hSet.law q hq _ _
  obtain ⟨c, hc⟩ := hF (G D p) (P D p) h mu hSet ν hν (hermS D p e) lam (cell e) τ w
    (fun y => nb y.1) hcell (fun y => (hInv nb hnb w hw y.1).1) hrel hnull
  have hOn : ∀ f, IsRho f → (∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g) →
      OnCell h (cell e) τ w (fun y => nb y.1) f := by
    intro f hf hfK x hx
    obtain ⟨q, hq, u, hu, ex, -⟩ := hdec x hx
    have hsec := (hRho f).mp hf
    have hf1 : f x = f (q * (w * nb (τ x).1)) := (congrArg f ex).trans (hfK u hu _)
    have hh1 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    show f x * h (w * nb (τ x).1) = f (w * nb (τ x).1) * h x
    rw [hf1, hh1]
    exact hsec.2 q hq _
  by_cases hc0 : c = 0
  · left
    intro f hf hfK
    have hmu' := (hc f ((hRho f).mp hf) (hOn f hf hfK)).2
    rw [hmu', hc0, zero_smul, integral_zero_measure]
  · right
    refine ⟨c, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf hfK => ?_⟩
    obtain ⟨hi, heq⟩ := hc f ((hRho f).mp hf) (hOn f hf hfK)
    refine ⟨?_, ?_⟩
    · have hi' := hi.smul_measure_nnreal (c := c⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hi'
    · rw [heq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end PositivityTheory.Rg.Rsw.Cell

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop

section

@[expose] public section

namespace PositivityTheory.Rg.Rsw.Cell

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem muCell : HtExist → IdemEx → MuCell := fun hH hI =>
  have hU := GlobalTheory.CompanionTheory.UnitCell.unitCrit hI
  have hA := GlobalTheory.CompanionTheory.CellTop.cellAlg hI
  muCell_of GlobalTheory.CompanionTheory.RswCell.riesz (GlobalTheory.CompanionTheory.RswCell.NullCompl.nullC_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) (GlobalTheory.CompanionTheory.RswCell.cellFormula_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) hA (GlobalTheory.CompanionTheory.CellDecomp.decomp hI)
    (GlobalTheory.CompanionTheory.CellFew.fewC hI hU (GlobalTheory.CompanionTheory.MoveCell.move_of_unitCrit hU) (GlobalTheory.CompanionTheory.SmallRatCell.smallRat hI) hA) (GlobalTheory.CompanionTheory.SetCell.setC hH) GlobalTheory.CompanionTheory.RswTop.topC

end PositivityTheory.Rg.Rsw.Cell
end
end
