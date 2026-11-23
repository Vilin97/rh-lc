module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBirationalRatioClosure
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagArith

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem HodgeFlagArith.proof (hNe : HodgeFlagNeZero.Statement) (hTr : HodgeFlagRatioTrdeg.Statement) :
    HodgeFlagArith.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  choose cX hcX using D.arith.2.1.2.2
  choose cP hcP using hNe II Ψ K ι Ω E D Pl H B
  let c : ∀ k, Pl.ιY k := fun
    | Sum.inl k => cX k
    | Sum.inr q => cP q.1 q.2
  have hc : ∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0 := by
    rintro (k | q)
    · intro h
      have h0 : D.y ⟨k, cX k⟩ = 0 := by
        have h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0 := h
        have h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0 :=
          IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')
        exact C_injective _ _ (h2.trans C_0.symm)
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    · exact hcP q.1 q.2
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : CharZero Pl.ΩY :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)
  have hhor : IsHorizontal (Pl.flagPrime B) := horizontal (Pl.flagGenericPoint B)
  refine ⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (Pl.flagGenericPoint B),
    relevant (Pl.flagGenericPoint B) c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ Pl.ιY (ratioField (Pl.flagGenericPoint B) c) (ratioPtL (Pl.flagGenericPoint B) c)
    (birational (Pl.flagGenericPoint B) c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField (Pl.flagGenericPoint B) c) = ((D.n + D.flagDim0 : ℕ) : Cardinal) := by
    rw [← hTr II Ψ K ι Ω E D Pl H B c hc]
    have hsub : (ratioField (Pl.flagGenericPoint B) c).toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      simp only [IntermediateField.adjoin_toSubfield]
      refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
        (Subfield.closure_mono Set.subset_union_right)
      rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    rw [← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]
    exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv
  rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc, hL] at htr
  have : (mCoordIdeal (Pl.flagGenericPoint B)).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) (algebraMap_injective _ hhor)
  show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) = _
  rw [hA, htr]
  rw [← Nat.cast_add, Cardinal.toENat_nat,
    show D.n + 1 + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) =
      D.n + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagNeZero

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HodgeFlagNeZero.proof : HodgeFlagNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical

  let BE : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  let w : ⋀[Ω]^((i : ℕ) + 1) (E τ) := exteriorPower.ιMulti Ω _ (B.e τ ∘ Fin.castLE (step_le i))
  have hw : w ≠ 0 := by
    have h := (BE.exteriorPower ((i : ℕ) + 1)).ne_zero
      (Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (step_le i)))
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Equiv.symm_apply_apply] at h
    convert h using 2
    funext x
    simp [BE, Fin.castLEOrderEmb]

  choose cX hcX using D.arith.2.1.2.2
  have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
    intro k h0
    apply hcX k
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hsum
    · exact h
  obtain ⟨b, -, hbspan, hA⟩ := hPr ⟨0, hM⟩
  have : Module.Finite Ω (E τ) := Module.Finite.of_basis BE
  have hbi : LinearIndependent Ω b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hbspan.ge
      (by rw [Module.finrank_eq_card_basis BE])
  let Bw := (Module.Basis.mk hbi hbspan.ge).exteriorPower ((i : ℕ) + 1)

  have hm : ∃ m, Pl.gen τ i m w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine Bw.forall_coord_eq_zero_iff.1 fun t => ?_
    obtain ⟨a, -, ha⟩ := hA _ (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono
    let ψ : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) :=
      ∑ m, (a m * chartMono D.y cX (-Pl.bdeg τ i)) • Pl.gen τ i m
    have hψ : ψ = Bw.coord t := by
      refine Bw.ext fun u => ?_
      have h1 := ha _ (Set.powersetCard.ofFinEmbEquiv.symm u).strictMono
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [Bw, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ψ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coe_mk]
      calc ∑ m, a m * chartMono D.y cX (-Pl.bdeg τ i) * Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u))
          = ∑ m, a m * (Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u)) * chartMono D.y cX (-Pl.bdeg τ i)) :=
            Finset.sum_congr rfl fun m _ => by ring
        _ = _ := h1
        _ = _ := by
          by_cases htu : t = u
          · subst htu
            simp
          · rw [if_neg fun h' =>
              htu (Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')).symm]
            simp [Ne.symm htu]
    rw [← hψ]
    simp [ψ, hcon]
  obtain ⟨m0, hm0⟩ := hm

  refine ⟨m0, ?_⟩
  let c0 : Fin ((i : ℕ) + 1) → Fin D.N := Fin.castLE (step_le i)
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (B.e τ ∘ c))
  let z : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω := fun c =>
    ∏ a, if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (z c * g c)
  have hP : Pl.pluecker0 B τ i m0 = algebraMap _ Pl.ΩY P := by

    simp only [PlueckerData.pluecker0, PlueckerData.gvar0, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hfac : ∀ a, (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then (0 : Pl.ΩY)
        else algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, headIdx (step_le i) a, c a))) =
        algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
          (C (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1) *
            X (τ, headIdx (step_le i) a, c a)) := by
      intro a
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun a _ => hfac a, ← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (z c * g c) = C (z c * g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, Finset.prod_mul_distrib]
    simp only [z, g, map_mul, map_prod, v, MvPolynomial.X]
    ring
  have hμ : ∀ c, μ c = μ c0 → c = c0 := by
    intro c h
    funext a
    have h2 := congrArg (fun φ : (Ψ × Fin D.N × Fin D.N) →₀ ℕ => φ (τ, headIdx (step_le i) a, c0 a)) h
    simp only [μ, v, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq,
      true_and, headIdx, Fin.castLE_inj] at h2
    rw [Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp),
      Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp)] at h2
    by_contra hne
    simp [hne] at h2
  have hz : z c0 = 1 :=
    Finset.prod_eq_one fun a _ => if_neg fun h => lt_irrefl _ (h.1.trans_le h.2)
  have hcoeff : AddMonoidAlgebra.coeff P (μ c0) = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl, hz, one_mul]
  have hPne : P ≠ 0 := fun h => hm0 (by simpa [h, g, c0, w] using hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioTrdeg

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioTrdeg.proof (h₂ : HodgeFlagRatioFieldEq.Statement) (h₃ : HodgeFlagMinorTrdeg.Statement) :
    HodgeFlagRatioTrdeg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  let cX : ∀ k, ι k := fun k => c (Sum.inl k)
  have hyX : ∀ p : Σ k, ι k, Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ = algebraMap Ω Pl.ΩY (D.y p) :=
    fun p => PlueckerData.ofΩ_eq Pl _
  have hcX : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := fun k h => hc (Sum.inl k) (by
    rw [hyX ⟨k, cX k⟩, h, map_zero])

  have hbase : Set.range (algebraMap Ω Pl.ΩY) ⊆ Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    have hle : Subfield.map (algebraMap Ω Pl.ΩY) (Subfield.closure (coneRatios D.y cX)) ≤
        Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro _ ⟨p, rfl⟩
      refine Subfield.subset_closure ⟨⟨Sum.inl p.1, p.2⟩, ?_⟩
      show Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ / Pl.flagGenericPoint B ⟨Sum.inl p.1, cX p.1⟩ =
        algebraMap Ω Pl.ΩY (D.y p / D.y ⟨p.1, cX p.1⟩)
      rw [map_div₀, hyX p, hyX ⟨p.1, cX p.1⟩]
    rintro _ ⟨x, rfl⟩
    refine hle ⟨x, ?_, rfl⟩
    rw [BirationalRatioClosure.full K ι Ω D.y cX D.birational hcX]
    trivial
  set Ef := IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c)
  have hsub : Ef.toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    rw [IntermediateField.adjoin_toSubfield]
    exact le_antisymm (Subfield.closure_le.2 (Set.union_subset hbase Subfield.subset_closure))
      (Subfield.closure_mono Set.subset_union_right)
  have e : Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) ≃+* Ef :=
    (RingEquiv.subfieldCongr hsub).symm.trans (RingEquiv.refl Ef)
  have hE : Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = Algebra.trdeg ℤ Ef :=
    (AlgEquiv.ofRingEquiv (f := e) fun x => by rw [eq_intCast, eq_intCast, map_intCast]).trdeg_eq
  rw [hE]
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr Int.cast_injective
  have : FaithfulSMul Ω Ef := (faithfulSMul_iff_algebraMap_injective Ω Ef).mpr (algebraMap Ω Ef).injective
  rw [← trdeg_add_eq ℤ Ω (A := Ef), FnFieldTrdeg.full K ι Ω D.y D.n D.birational D.arith,
    ← (IntermediateField.equivOfEq (h₂ II Ψ K ι Ω E D Pl H B c hc)).symm.trdeg_eq,
    h₃ Ω Ψ D.N D.j D.j_le_N]
  rw [← Nat.cast_add]
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushDown.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hArith : HodgeFlagArith.Statement) : PushDown.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep
  have hY := hArith II Ψ K ι Ω E D Pl H B
  have hX : IsArithVar (imageZ Pl.xV (Pl.flagPrime B)) (D.n + 1) := by
    rw [Pl.imageZ_forget_flagPrime]
    exact D.arith
  refine ⟨fun G J L L' N hJ hL hL' hN => ?_, fun d r L L' N hdr hd hL hL' hN => ?_⟩
  · have h := hPF II hII.1 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) D.flagDim0
      G J L L' N Pl.isBlockMap_xV hY hX hJ hL hL' hN
    rwa [Pl.imageZ_forget_flagPrime] at h
  · exact hII.2.2.2 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) d r L L' N
      Pl.isBlockMap_xV (by rw [hdr]; exact hY) hX hd hL hL' hN

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystemStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
end
end
