module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfBddInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfStokesFn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfTwLie
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfBddInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfLevInv
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfRapidBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PtZsmulRight

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfAdjInt

section

@[expose] public section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.adjInt :
    UpperTheory.V.Lit.Geo.Pf.AdjInt := by
  intro E _ _ _ a μ _ Ξ r χ G htw hadm X x y hx hy hs
  have hint : ∀ u v, Pf.TwInv χ u → Pf.TwInv χ v → Pf.Cs (Pf.pt χ G u v) → Pf.QInt μ (Pf.pt χ G u v) :=
    fun u v hu hv hc =>
      have hC := (Pf.ptInv E a χ _ G u v).2.1 hu hv
      (Pf.bddInt E a μ _ hC (Pf.csBdd E a _ hC (.inl hc))).1
  refine (fun (h : _ ∧ _) (h3 : _ ∧ _ → _) => ⟨h.1, h.2, h3 h⟩) ⟨?_, ?_⟩ ?_
  · exact hint _ _ hx (Pf.twLie E a Ξ r χ htw _ y hy).1
      (hs.elim (fun h => Pf.cs_pt_left χ G _ h)
        fun h => Pf.cs_pt_right χ G _ (Pf.csTens E a Ξ r _ y h).1)
  · exact hint _ _ (Pf.twLie E a Ξ r χ htw _ x hx).2 hy
      (hs.elim (fun h => Pf.cs_pt_left χ G _ (Pf.csTens E a Ξ r _ x h).2)
        fun h => Pf.cs_pt_right χ G _ h)
  rintro ⟨h1, h2⟩
  obtain ⟨θ, hθ, hd⟩ := Pf.ptDiv E a Ξ r χ G htw hadm x y
  have hS := (Pf.ptInv E a χ _ G x y).2.2 θ hθ hx hy
  have hc : Pf.Cs θ.1 := by
    rw [show θ.1 = _ from funext hθ]
    exact hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ h
  have h0 := fun Y => Pf.stokesFn E a μ θ Y hS hc
  refine sub_eq_zero.1 ?_
  unfold Pf.qint at h0 ⊢
  rw [← MeasureTheory.integral_sub h1 h2]
  simp only [← hd X]
  exact h0 _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtPos

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfZeroInt

section

@[expose] public section

open UpperTheory.V.Lit.Geo
open NumberField MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem UpperTheory.V.Lit.Geo.Pf.zeroInt :
    UpperTheory.V.Lit.Geo.Pf.ZeroInt := by
  intro E _ _ _ a μ _ F hF hpos hI h0
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) F := CuspidalL2GL.leftInv_latticeGL hF.left hF.centre
  have hn : ∀ g, F g = ((‖F g‖ : ℝ) : ℂ) := fun g => by
    obtain ⟨t, ht, e⟩ := hpos g
    rw [e, Complex.norm_real, Real.norm_of_nonneg ht]
  have h1 : ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) = 0 := by
    have h2 : Pf.qint μ F =
        ((∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hn _)
    rw [h0] at h2
    exact_mod_cast h2.symm
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) (Integrable.norm hI)).1 h1
  have h4 : F =ᵐ[μ] fun _ => 0 := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h3] with g hg
    have e : F (GlobalTheory.AutomorphicL2Unitary.mk (latticeGL E a) g).out = F g := hL.descend_mk g
    simpa [e] using hg
  exact fun g => congrFun ((Continuous.ae_eq_iff_eq μ hF.cont continuous_const).1 h4) g
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFacts

section

@[expose] public section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.pairFacts :
    PairFacts :=
  Pf.pairFacts_of_steps Pf.bddInt Pf.csBdd Pf.levInv Pf.ptInv Pf.adjInt Pf.ptD Pf.rapidBdd Pf.zeroInt Pf.ptPos
end
end
