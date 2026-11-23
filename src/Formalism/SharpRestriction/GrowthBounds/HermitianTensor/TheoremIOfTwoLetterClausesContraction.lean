module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudADef
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfLatticeFunctorComparison
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
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
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudB
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem cloudOne_of (h : ContractionStandardLattice) : CloudOne := by
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  obtain ⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩ := h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hm1 : 1 ≤ mm + 1 := by omega
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := cc_dualWt_anti _ hloA
  have hmuA : Antitone (wtPQ (mm + 1) P Q) := wtPQ_anti _ _ _ hm1
  have hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_left rfl]
  have hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_right (caLast_ne_zero mm), ite_eq_left rfl]
  have hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    unfold dualWt
    rw [Fin.rev_last, hlo0]
  refine ⟨abelian₂, hK, ?_, ?_⟩
  · rintro Λ ⟨g, hg, rfl⟩ v hv t ht
    rw [mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]
    have hv0 := (mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv
    have ht0 := (mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht
    have hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) :=
      la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)
    have htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
      la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)
    have h3 := hI _ hv0 _ ht0
    rw [map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero] at h3
    have he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) =
        wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1)) := by
      rw [hl, hloL', wtPQ_last]
      push_cast
      ring
    rwa [he] at h3
  · intro g hg
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))),
      fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩
    · intro a' b F hF
      have hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)) :=
        dualWeylRowStable R.Kf _ _ _ g F hF
      have e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b) := by
        rw [map_mul, rowAct_cancel_inv g hg, mul_smul_comm]
      have hsK := intO_le (O := R.O) _ _ _ (hs b).1
      have hsK' := intO_le (O := R.O) _ _ _ (hs' a').1
      have hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) := by
        have h4 := dualWeyl_mul R.Kf _ _ _ _ hF0 hsK
        rw [← nuOf_add _ _ hmuA hloA] at h4
        have e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam := by abel
        rwa [e] at h4
      show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) *
        blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _
      rw [e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]
      split_ifs
      · rw [map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]
        congr 1
        ring
      · rw [map_zero, smul_zero]
    · intro c hc
      have hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det := by
        rw [Matrix.det_mul]
        exact hg.mul (lb_D_det _ 1 c hc)
      have hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl) := by
        have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)
        have h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl := by
          unfold nuOf
          rw [wtPQ_zero, wtPQ_last]
          omega
        rwa [h6] at h5
      have hcz := core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]
        exact hw_int _ _ (nuOf_anti _ hzeA)
      · rintro ⟨z', hz', he⟩
        have h7 := (mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'
        rw [wtPQ_last] at h7
        apply hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))
        refine ⟨_, h7, ?_⟩
        rw [← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]
      · intro b
        have hR : Row0 (s b) (ccl + ccl) := by rw [← two_mul]; exact (hs b).2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]
        exact (hs b).1
      · intro a'
        have hR : Row0 (s' a') (ccl + ccl) := by rw [← two_mul]; exact (hs' a').2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]
        exact (hs' a').1

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudC

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

section

variable {p n' : ℕ} {R : RS p n'} {m : ℕ}

theorem cc_elem (X : Fin n' → Fin (m + 1) → ℤ) (e : Edge R.W R.Qq (m + 1))
    (G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)
    (hs : (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src) = famD R.O G 1)
    (hle : (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e) = famD R.O G (algebraMap R.O R.Kf R.w))
    (x : Vsp R.Kf X) (h1 : ((1 : R.Kf) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G 1)))
    (hw : ((algebraMap R.O R.Kf R.w) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G (algebraMap R.O R.Kf R.w)))) :
    x ∈ HL (O := R.O) R.ι R.σ X e.src ∧ x ∈ Re p R.ι R.σ R.w 1 X e := by
  constructor
  · show x ∈ toV X (Hten R.O X (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src))
    rw [hs]
    rwa [one_zpow, one_smul] at h1
  · refine (cc_mem_scale (zpow_ne_zero _ R.w_ne)).2 ?_
    rw [zpow_neg, inv_inv]
    show _ ∈ toV X (Hten R.O X (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
    rw [hle]
    exact hw

end

theorem restCloudMaps_of (h : RestCloudLat) (hIncl : DualHeightInclusion) : RestCloudMaps := by
  classical
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨mH, mU, abelian₂, hint, hel⟩ :=
    h p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨G, hG, hs, hle, ht⟩ := cc_edge R e he
  obtain ⟨nb, z0, s, s', ka, hnb, hka, h24, hmem⟩ := hel G hG
  have hw : algebraMap R.O R.Kf R.w ≠ 0 := R.w_ne
  have hIH : IntB R mH := fun M hM => (hint M hM).1
  have hIU : IntB R mU := fun M hM => (hint M hM).2.1
  have hIL : IntB R abelian₂ := fun M hM => (hint M hM).2.2

  obtain ⟨hlo1, hlo2⟩ := cc_lo TT ccl aw bw lam0 A B hBase hzero hAB
  obtain ⟨hlo1', hlo2'⟩ := cc_dualW TT _ _ hlo1 hlo2
  have hze1 : ∀ s ∈ TT, flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s 0 = ((2 * ccl : ℕ) : ℤ) ∧
      flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s (Fin.last (mm + 1)) = -((2 * ccl : ℕ) : ℤ) :=
    fun s hs => ⟨cc_flat_zero _ _ _ s hs, cc_flat_last _ _ _ s hs⟩
  obtain ⟨aze, -⟩ := cc_Ar_of TT _ _ hze1 (fun s hs => cc_flat_off _ _ _ s hs)
  obtain ⟨alo, -⟩ := cc_Ar_of TT _ _ hlo1 hlo2
  obtain ⟨alo', elo'⟩ := cc_Ar_of TT _ _ hlo1' hlo2'
  have aHp : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 (flatW (mm + 1) A B) + Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) := by
    rw [← cc_Ar_add, ← cc_flat_add]
  have alam : Ar 1 lam0 = Ar 1 (flatW (mm + 1) A B) + Ar 1 (lam0 - flatW (mm + 1) A B) := by
    rw [← cc_Ar_add, add_sub_cancel]
  have aL : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 lam0 + Ar 1 (dualW (lam0 - flatW (mm + 1) A B)) := by
    rw [aHp, alam, aze, alo, alo']
    push_cast
    ring
  have hdlo : IsDominant (lam0 - flatW (mm + 1) A B) := cc_lo_dom TT ccl aw bw lam0 A B hBase hDom hzero hAB
  have hdlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := fun s => cc_dualWt_anti _ (hdlo s)

  obtain ⟨z1, sb1, sa1, -⟩ := hmem 1 one_ne_zero
  obtain ⟨zw, sbw, saw, isow⟩ := hmem _ hw
  obtain ⟨-, -, sap, -⟩ := hmem _ (mul_ne_zero hw hw)
  obtain ⟨hz1, hz2⟩ := cc_elem _ e G hs hle z0 z1 zw
  refine ⟨nb, mH.flip z0, fun b => mU.flip (s b), fun a' => abelian₂.flip (s' a'), ka, hnb, hka, ?_, ?_, ?_⟩
  · intro a' b F
    exact h24 a' b F
  · intro F
    constructor
    · intro hF
      have h1 := (cc_mem_scale (zpow_ne_zero _ hw)).1 hF
      rw [zpow_neg, inv_inv] at h1
      have h2 : mH ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F)
          ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl))) • z0) =
          (algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) •
            mH.flip z0 F := by
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← zpow_add₀ hw, aHp, LinearMap.flip_apply,
          add_comm (Ar 1 (flatW (mm + 1) A B))]
      have h3 := isow ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F) (by
        rw [h2, ← hle]
        exact h1)
      refine (cc_mem_scale (zpow_ne_zero _ hw)).2 ?_
      rw [zpow_neg, inv_inv]
      show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
      rw [hle]
      exact h3
    · intro hF
      exact cc_Re hIH aHp e he F hF z0 hz2
  · intro t c₂ hc
    refine ⟨?_, ?_, ?_⟩
    · intro F hF
      exact cc_CCL hIncl hIH aHp (flattened_weight_dominant _ _ _) e he z0 hz1 hz2 t c₂ F hF
    · intro b F hF
      obtain ⟨hb1, hb2⟩ := cc_elem _ e G hs hle (s b) (sb1 b) (sbw b)
      exact cc_CCL hIncl hIU alam hdlo e he (s b) hb1 hb2 t c₂ F hF
    · intro a' g hg
      obtain ⟨-, ha2⟩ := cc_elem _ e G hs hle (s' a') (sa1 a') (saw a')
      have ha3 : ((algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) ^ Ar 1 (dualW (lam0 - flatW (mm + 1) A B))) • s' a' ∈
          HL (O := R.O) R.ι R.σ (dualW (lam0 - flatW (mm + 1) A B)) e.tgt := by
        show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => extO R.O R.ι R.σ s.val e.tgt))
        rw [ht]
        exact sap a'
      have h5 := cc_CCL' hIL aL hdlo' (by rw [elo', alo']) (TT.card * ccl) (by rw [alo']; push_cast; ring) e he (s' a')
        ha3 ha2 t c₂ (by rw [← mul_assoc]; exact hc) g hg
      rw [← mul_assoc] at h5
      exact h5

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem cloud_maps_of_contraction (hQ : ContractionStandardLattice) (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  restCloudMaps_of (restCloudLat_of (cloudOne_of hQ) hCO (cloudIso hCD hCO)) hIncl

theorem theorem_I_of_two_letter_clauses_contraction (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hQ : ContractionStandardLattice) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  exact theorem_I_of_explicit_minor_map D (tiePsi_of D h1 h2 h5 h11.2 h16.1) (cloud_maps_of_contraction hQ h11.1 h11.2 h13.2.1) hA

end Formalism.MainNotions.flipOneThree.Pf
end
end
