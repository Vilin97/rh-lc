module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudB
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudC
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem cloud_maps_of_contraction (hQ : ContractionStandardLattice) (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  restCloudMaps_of (restCloudLat_of (cloudOne_of hQ) hCO (cloudIso hCD hCO)) hIncl

open Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility in
theorem theorem_I_of_two_letter_clauses_contraction (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hQ : ContractionStandardLattice) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have hPsi : TiePsi := by
    intro p n' R m hm
    have hm1 : 1 ≤ m := by omega
    refine ⟨h1 R.Kf m hm1, h2 R.Kf m hm1, ?_, ?_, ?_⟩
    · intro a b y
      rw [← tie3 h2 h5 h11.2 R m hm1 a b]
      exact Submodule.mem_map
    · intro a b
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have : CharZero R.Kf := R.charZero
      have : Module.Finite R.Kf (PolAB R.Kf (k + 2) a b) := Har2.finite_polAB (k + 1) a b
      set T := (dPsi R.Kf (k + 1)).domRestrict (PolAB R.Kf (k + 2) a b) with hT
      have hrange : LinearMap.range T = dualWeyl R.Kf (k + 2) (k + 2) (nuOf (wtPQ (k + 1) a b)) := by
        rw [hT, LinearMap.range_domRestrict]
        exact tie3 h2 h5 h11.2 R (k + 1) hm1 a b
      have hdim : Module.finrank R.Kf (dualWeyl R.Kf (k + 2) (k + 2) (nuOf (wtPQ (k + 1) a b))) =
          dimHar (k + 1) a b := by
        have hanti : Antitone (nuOf (wtPQ (k + 1) a b)) := by
          intro i j hij
          have := wtPQ_anti (k + 1) a b hm1 hij
          unfold nuOf
          omega
        have hweyl : (Module.finrank R.Kf (dualWeyl R.Kf (k + 2) (k + 2) (nuOf (wtPQ (k + 1) a b))) : ℚ) =
            weylDim (k + 2) (fun i => (nuOf (wtPQ (k + 1) a b) i : ℤ)) := by
          rw [h16.1 R.Kf _ _ hanti]
          unfold weylDim
          refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
          push_cast
          rfl
        simp_rw [nuOf_wtPQ_cast, weylDim_shift, weylDim_hwt_eq] at hweyl
        exact_mod_cast hweyl
      have hRank := LinearMap.finrank_range_add_finrank_ker T
      rw [hrange, hdim, Har2.finrank_polAB] at hRank
      intro f hf hf0
      have hfker : (⟨f, hf⟩ : PolAB R.Kf (k + 2) a b) ∈ LinearMap.ker T := hf0
      by_cases hab : a = 0 ∨ b = 0
      · have hzero : Module.finrank R.Kf (LinearMap.ker T) = 0 := by
          unfold dimHar dimPol at hRank
          rw [ite_eq_left hab] at hRank
          omega
        rw [Submodule.finrank_eq_zero.1 hzero, Submodule.mem_bot] at hfker
        have hfzero : f = 0 := congrArg Subtype.val hfker
        exact ⟨0, Submodule.zero_mem _, by rw [hfzero, mul_zero]⟩
      · rw [not_or] at hab
        obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        let μ : PolAB R.Kf (k + 2) a b →ₗ[R.Kf] PolAB R.Kf (k + 2) (a + 1) (b + 1) :=
          LinearMap.codRestrict _ ((LinearMap.mulLeft R.Kf (hXY R.Kf (k + 2))) ∘ₗ (PolAB R.Kf (k + 2) a b).subtype)
            (fun G => Har2.h_mul_mem G.2)
        have hμinj : Function.Injective μ := by
          intro G G' h
          have h' : hXY R.Kf (k + 2) * (G : PolXY R.Kf (k + 2)) = hXY R.Kf (k + 2) * G' :=
            congrArg Subtype.val h
          exact Subtype.ext (mul_left_cancel₀ (hXY_ne_zero R.Kf (k + 1)) h')
        have hle : LinearMap.range μ ≤ LinearMap.ker T := by
          rintro _ ⟨G, rfl⟩
          show deltaB R.Kf (k + 1) (PsiXY R.Kf (k + 1) (hXY R.Kf (k + 2) * (G : PolXY R.Kf (k + 2)))) = 0
          rw [map_mul, map_mul, delta_Psi_h R.Kf (k + 1) hm1, zero_mul]
        have hRange : Module.finrank R.Kf (LinearMap.range μ) = (a + (k + 1)).choose (k + 1) * (b + (k + 1)).choose (k + 1) := by
          rw [LinearMap.finrank_range_of_inj hμinj, Har2.finrank_polAB]
        have heq : LinearMap.range μ = LinearMap.ker T := by
          apply Submodule.eq_of_le_of_finrank_eq hle
          rw [hRange]
          unfold dimHar dimPol at hRank
          rw [ite_eq_right (by omega)] at hRank
          simp only [Nat.add_sub_cancel] at hRank
          have hchooseLe : (a + (k + 1)).choose (k + 1) * (b + (k + 1)).choose (k + 1) ≤
              (a + 1 + (k + 1)).choose (k + 1) * (b + 1 + (k + 1)).choose (k + 1) :=
            Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
          exact (Nat.add_left_cancel (hRank.trans (Nat.sub_add_cancel hchooseLe).symm)).symm
        rw [← heq] at hfker
        obtain ⟨G, hG⟩ := hfker
        exact ⟨G, G.2, (congrArg Subtype.val hG).symm⟩
    · rintro Λ ⟨g, hg, rfl⟩
      have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
      refine ⟨Matrix.GeneralLinearGroup.mk'' g⁻¹ hgi, ?_, ?_⟩
      · intro P Q f hf
        exact h5 p n' R m hm1 g hg _ rfl P Q f hf
      · intro a b y
        exact tie5b h2 h5 h11.2 R m hm1 g hg _ rfl a b y
  exact theorem_I_of_explicit_minor_map D hPsi (cloud_maps_of_contraction hQ h11.1 h11.2 h13.2.1) hA

end Formalism.MainNotions.flipOneThree.Pf
