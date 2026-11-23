module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionBlockEmb
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Linter.Style
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
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DerivativeRepresentation
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ExplicitMapOntoTwoLetterSpace
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.InitialMinorLiftFirstEntry
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubCoeffP
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TopLinePOf
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TwoLetterLatticeGaussInverse

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ContractionOfPairingLemmas

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem contraction_of_pairing_lemmas (hPh : QPh) (hSC : SubCoeffP) (hSM : SubMapP) (hSR : SubRowP) (hLC : LamCoeffP) (hLE : LamEquivP)
    (hLM : LamMulP) (hLV : LamEvalP) (hMem : LamMemP) (hMu : SubMuP) (hTop : TopLineP) (hLift : LiftP) (hDD : DetDivP)
    (hIC : IntCapP) (hHw : HwMulP) : ContractionStandardLattice := by
  classical
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have := R.charZero
  have : Infinite R.Kf := inferInstance
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := qsDualWt_anti _ hloA
  have hαZ := nuOf_lam_mid mm ccl Q lam hl hmid
  have hβZ := nuOf_lo_mid mm ccl P Q lam h0 hl hmid
  have hβ'Z := nuOf_lo'_mid mm ccl P Q lam h0 hl hmid
  have hbd := lam_mid_bd mm ccl lam hmid
  have hαA : Antitone (fun j => nuOf lam (midI mm j)) := fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)
  have hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl := by
    intro i
    show nuOf lam (midI mm i) ≤ Q + 2 * ccl
    have := hαZ i; have := hbd i; omega
  have hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl := by
    intro i j
    show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl
    have := hαZ i; have := hαZ j; have := hbd i; have := hbd j; omega
  obtain ⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩ :=
    hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8
  have hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) =
      fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) := by
    funext j
    show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _
    have h1 := hβ'Z j; have h2 := hαZ j.rev; have h3 := hbd j.rev; omega
  rw [hα'] at hInv hInt hu'
  have hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q := by
    funext j
    have := hαZ j; have := hβZ j; omega
  have hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b)) := fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))
  have hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
      ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) :=
    hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))
      (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _)
      (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
      (fun j => nuOf_wt_mid mm _ _ j) hInv
  refine ⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩
  · intro v hv t ht
    refine hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_
    intro x
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := ht
    have e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0 := rfl
    have e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0 := rfl
    rw [hLC, e1, e2, hSM, hSM]
    have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x,
        L (blockEmb R.Kf true (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0)) y.1) *
          blockEmb R.Kf false (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0)) y.2))) ∈
        (algebraMap R.O R.Kf).range := by
      refine sum_mem fun y _ => ?_
      rw [coeff_map, coeff_map]
      exact hInt _ ⟨AddMonoidAlgebra.coeff (subY R.O mm v0) y.1, hSC R.O mm _ v0 hv0 _, rfl⟩ _
        ⟨AddMonoidAlgebra.coeff (subY R.O mm t0) y.2, hSC R.O mm _ t0 ht0 _, rfl⟩
    exact this
  · have hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)
    have hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl
      have := hβZ j; have := hbd j; omega
    have hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)
    have hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl
      have := hβ'Z j; have := hbd j.rev; omega
    have hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧
          map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b := by
      intro b
      obtain ⟨f, hf, hfe⟩ := hu b
      rw [hαβ] at hf
      obtain ⟨w0, hw0, rfl⟩ := hDD R.O mm Q _ hmm hβA f hf
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0
      rw [shapeC_lo mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    have hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a' := by
      intro a'
      obtain ⟨f, hf, hfe⟩ := hu' a'
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf
      rw [shapeC_lo' mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    choose s0 hs0 hs0r hs0l hs0e using hS
    choose t0 ht0 ht0r ht0l ht0e using hS'
    refine ⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka,
      fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩
    · have e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl) := by
        funext j
        rw [hαZ j]; ring
      rw [hnb, e]
      exact weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)
    · intro a' b F hF
      have e1 := hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a'))
        (hMu p n' R mm hmm P Q F hF)
      have hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q)) := hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)
      have hF0sub := hMu p n' R mm hmm 0 Q _ hF0
      have e2 := hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub
      have hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)
      have hTK : map (algebraMap R.O R.Kf) (t0 a') ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')
      have hInv' : PhInv R.Kf mm (Q + 2 * ccl)
          (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j))
          (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L := by
        have e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
            fun j => nuOf lam (midI mm j) := by
          funext j
          rw [Pi.add_apply, nuOf_wt_mid]
          have := hαZ j; have := hβZ j; omega
        rw [e]; exact hInv
      have hΨmem := hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q))
        (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L
        (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _)
        (by rw [nuOf_wt_zero, Pi.add_apply, nuOf_wt_zero, nuOf_lo_zero mm ccl P Q lam h0 hl,
              nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
        (fun j => nuOf_wt_mid mm _ _ j) hInv' _ (dualWeyl_mul R.Kf _ _ _ _ hF0 hSK) _ hTK
      have hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) 0
        rwa [nuOf_wt_zero, zero_add] at h
      have hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0 := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))
        rwa [nuOf_last] at h
      have hΨ0 := rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _
        (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b)))
        (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))
      have hΨl := rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _
        (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b)))
        (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))
      have ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl) := by omega
      rw [ed] at hΨ0
      have hΨ := hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl
      have hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q := by
        unfold resY
        rw [hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]
      have hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1))
          (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) *
            map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) =
          if a' = b then (p : R.Kf) ^ ka b else 0 := by
        have hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b)) := by
          rw [← hs0e b, map_mul, map_pow, detY_map]
        rw [hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]
      have hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) =
          nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q) := by
        have := nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q
        rwa [add_zero, add_comm (2 * ccl) Q] at this
      rw [hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1] at hΨ
      have hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0 := hwNe R.Kf _ _ le_rfl _
      have hΦ := mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)))
        (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))))
        (by rw [← e2, hΨ]; ring)
      rw [e1, hΦ]
      split_ifs
      · rw [smul_eq_C_mul]; ring
      · rw [C_0, zero_mul, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsP

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems
open scoped TensorProduct

theorem bilinP : BilinP := by
  classical
  intro K _ r B
  let g : Bool → MvPolynomial (Fin r × Fin r) K →ₗ[K]
      (MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K) := fun b =>
    match b with
    | true => (Algebra.TensorProduct.includeLeft :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
    | false => (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
  obtain ⟨F, hF⟩ := KP.tensorMap (K := K) (S := Bool) (α := Fin r × Fin r) g
  refine ⟨(TensorProduct.lift B) ∘ₗ F, ?_⟩
  intro f f'
  have h := hF (fun b => match b with | true => f | false => f')
  rw [Fintype.prod_bool, Fintype.prod_bool] at h
  have h' : F (blockEmb K true f * blockEmb K false f') = f ⊗ₜ[K] f' := by
    refine h.trans ?_
    show (f ⊗ₜ[K] (1 : MvPolynomial (Fin r × Fin r) K)) * ((1 : MvPolynomial (Fin r × Fin r) K) ⊗ₜ[K] f') = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [LinearMap.comp_apply, h', TensorProduct.lift.tmul]

theorem detFactsP : DetFactsP := by
  intro A _ r e
  constructor
  · have h1 : detY A r ∈ dualWeyl A r r (qcOm r r) := by
      rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
      exact qc_initMinor_mem A id le_rfl
    have h2 := qc_pow_mem A r r _ _ h1 e
    have e1 : e • qcOm r r = fun _ => e := by
      funext t
      simp [qcOm, t.isLt]
    rwa [e1] at h2
  · intro l
    unfold detY
    have hA := AlgHom.map_det (rowAct A (n := r) l) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
    have hM : (rowAct A (n := r) l).mapMatrix (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) =
        (C : A →+* MvPolynomial (Fin r × Fin r) A).mapMatrix l *
          (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply]
      show rowAct A l (X (i, j)) = ∑ b, C (l i b) * X (b, j)
      simp [rowAct]
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, ← RingHom.map_det]
    rfl

theorem numP : NumP := by
  intro p a c r ell hp hr hl hc
  unfold N0 deF kappaOneExponent lgA
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hN : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
    have h0 : r * (r - 1) / 2 ≤ (r + 1) ^ 2 := by
      calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
        _ ≤ (r + 1) * (r + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (r + 1) ^ 2 := by ring
    exact_mod_cast h0
  have h1 : Nat.log p (ell + r - 1) ≤ Nat.log p (8 * a + (r + 1)) := Nat.log_mono_right (by omega)
  have h2 : (Nat.log p (8 * a + (r + 1)) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) := by
    first
    | exact Real.natLog_le_logb _ _
    | (have hpow := Nat.pow_log_le_self p (x := 8 * a + (r + 1)) (by omega)
       rw [Real.le_logb_iff_rpow_le hp1 (by positivity)]
       exact_mod_cast hpow)
  have h3 : (Nat.log p (ell + r - 1) : ℝ) ≤ Nat.log p (8 * a + (r + 1)) := by exact_mod_cast h1
  have hL : (Nat.log p (ell + r - 1) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) + 1 := by linarith
  push_cast at hL hN
  have key : ((r * (r - 1) / 2 * Nat.log p (ell + r - 1) : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) ^ 2 * (Real.logb p (8 * (a : ℝ) + ((r : ℝ) + 1)) + 1) := by
    push_cast
    exact mul_le_mul hN hL (Nat.cast_nonneg _) (by positivity)
  have key2 := key.trans (Nat.le_ceil _)
  push_cast at key2 ⊢
  exact_mod_cast key2

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYDPsiMonomial

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dite_eq_right]
  simp

theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]

  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ModelIdentificationHolds

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_of_rest (hTau : TauP) (hSm : SmithP) : QPh :=
  qPh_of hTau hSm bilinP detFactsP numP detDivP

theorem contraction_of_pairing_GL (hPh : QPh) (hCO : CartanOnto) : ContractionStandardLattice :=
  contraction_of_pairing_lemmas hPh subCoeffP subMapP subRowP lamCoeffP lamEquivP lamMulP lamEvalP lamMemP
    (subMuP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) (topLineP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) liftP detDivP intCapP hwMulP

theorem theorem_I_of_contraction (D : Formalism.BasicNotions.D7) (hQ : ContractionStandardLattice) : SecondPartClosed D :=
  theorem_I_of_two_letter_clauses_contraction D explicit_map_injective explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hQ

theorem theorem_I_of_pairing_GL (D : Formalism.BasicNotions.D7) (hPh : QPh) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, -, h0⟩ := hA 0 le_rfl
  obtain ⟨T1, -, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, -, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, -, -, -, -, hB⟩ := h2 T2 le_rfl
  have hT : AdmT D := hB.2.2.2.2
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  exact theorem_I_of_contraction D (contraction_of_pairing_GL hPh h11.2) hA

end Formalism.MainNotions.flipOneThree.Pf
end
end
