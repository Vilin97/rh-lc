module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.FrobDense

theorem placesS_finite (D : D7) (l : ℕ) : (placesS D l).Finite := by
  have h0 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 1) (D.host.g_prime 1).ne_zero
  have h2 := Formalism.L2.TwC.placesOver_finite' D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)
    (by split_ifs <;> first | exact D.host.pde'_prime.ne_zero | exact D.host.pde_prime.ne_zero)
  refine ((h0.union h1).union h2).subset ?_
  rintro v ⟨hv | hv | hv, -⟩
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr hv)
  · exact Or.inr hv

theorem frob_dense_goodSplit : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  intro D l Q hl hC
  have hfin : (placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host))).Finite :=
    ((Formalism.L2.TwC.placesOver_finite' D.host.E l hl.ne_zero).union (placesS_finite D l)).union Q.finite_toSet
  refine (hC hfin.toFinset).mono ?_
  rintro σ ⟨w, hwS, hsp, B, hB, hF⟩
  have hw : w ∉ placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host)) := by
    simpa using hwS
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  exact ⟨w, ⟨hsp, hw.1.1, hw.1.2, hw.2⟩, B, hB, hF⟩

end GlobalTheory.FrobDense
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty


theorem _root_.GlobalTheory.T.dense_frobenius_goodSplitPlaces : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  first | exact @GlobalTheory.FrobDense.frob_dense_goodSplit | exact GlobalTheory.FrobDense.frob_dense_goodSplit | (intros; apply GlobalTheory.FrobDense.frob_dense_goodSplit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.IntegralModelOverCoeff

open scoped Matrix

theorem exists_integral_conj {l : ℕ} [Fact l.Prime] {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (a : ℕ) (ρ : Γ →* GL (Fin a) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hK : ∀ g s t, ∃ x, ι x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t) :
    ∃ (r : Γ →* GL (Fin a) O) (Pm : GL (Fin a) (Qbar l)),
      ∀ g, mapRep (ι.comp (algebraMap O (FractionRing O))) r g = Pm⁻¹ * ρ g * Pm := by
  classical
  set K := FractionRing O
  choose f hf using hK
  have hιi : Function.Injective (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro A B h
    ext s t
    exact ι.injective (congrFun (congrFun h s) t)
  have hM : ∀ g, ι.mapMatrix (Matrix.of (f g)) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; ext s t; exact hf g s t
  let ρ0 : Γ →* Matrix (Fin a) (Fin a) K :=
    { toFun := fun g => Matrix.of (f g)
      map_one' := hιi (by rw [hM, map_one, map_one, Units.val_one])
      map_mul' := fun g h => hιi (by rw [map_mul, hM, hM, hM, map_mul, Units.val_mul]) }
  let ρK : Γ →* GL (Fin a) K := ρ0.toHomUnits
  have hρK : ∀ g, ι.mapMatrix ((ρK g : GL _ _) : Matrix (Fin a) (Fin a) K) =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := fun g => hM g

  let Int : Set (Matrix (Fin a) (Fin a) (Qbar l)) := {M | ∀ s t, ‖M s t‖ ≤ 1}
  have hInt1 : (1 : Matrix (Fin a) (Fin a) (Qbar l)) ∈ Int := by
    intro s t
    by_cases h : s = t
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hIntMul : ∀ A B, A ∈ Int → B ∈ Int → A * B ∈ Int := by
    intro A B hA hB s t
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA s k) (norm_nonneg _) (hB k t)
  have hIntOpen : IsOpen Int := by
    have : Int = ⋂ s, ⋂ t, (fun M : Matrix (Fin a) (Fin a) (Qbar l) => M s t) ⁻¹' Metric.closedBall 0 1 := by
      ext M; simp [Int]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage (continuous_id.matrix_elem s t)
  let U : Subgroup Γ :=
    { carrier := {g | ((ρ g : GL _ _) : Matrix _ _ _) ∈ Int ∧ ((ρ g⁻¹ : GL _ _) : Matrix _ _ _) ∈ Int}
      one_mem' := by simp [hInt1]
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul]; exact hIntMul _ _ hg1 hh1
        · rw [mul_inv_rev, map_mul, Units.val_mul]; exact hIntMul _ _ hh2 hg2
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        exact ⟨h2, by rwa [inv_inv]⟩ }
  have hUopen : IsOpen (U : Set Γ) :=
    (hIntOpen.preimage hc).inter (hIntOpen.preimage (hc.comp continuous_inv))
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUint : ∀ h ∈ U, ∀ i j, ((ρK h : GL _ _) : Matrix (Fin a) (Fin a) K) i j ∈ (algebraMap O K).range := by
    intro h hh i j
    rw [GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι]
    have := congrFun (congrFun (hρK h) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    exact hh.1 i j
  obtain ⟨P, hP⟩ := GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.exists_conj_integral (O := O) a ρK U hUint
  choose e he using hP
  have hai : Function.Injective ((algebraMap O K).mapMatrix :
      Matrix (Fin a) (Fin a) O →+* Matrix (Fin a) (Fin a) K) := by
    intro A B h
    ext s t
    exact IsFractionRing.injective O K (congrFun (congrFun h s) t)
  have hE : ∀ g, (algebraMap O K).mapMatrix (Matrix.of (e g)) =
      ((P * ρK g * P⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
    intro g; ext s t; exact he g s t
  let r0 : Γ →* Matrix (Fin a) (Fin a) O :=
    { toFun := fun g => Matrix.of (e g)
      map_one' := hai (by rw [hE, map_one, map_one, mul_one, mul_inv_cancel, Units.val_one])
      map_mul' := fun g h => hai (by
        rw [map_mul, hE, hE, hE, ← Units.val_mul, map_mul]
        congr 1
        group) }
  refine ⟨r0.toHomUnits, (Units.map (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* _).toMonoidHom P)⁻¹, fun g => ?_⟩
  ext1
  rw [inv_inv]
  show (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) = _
  have : (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) =
      ι.mapMatrix ((algebraMap O K).mapMatrix (Matrix.of (e g))) := by
    ext s t; rfl
  rw [this, hE, Units.val_mul, Units.val_mul, map_mul, map_mul, hρK]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.IntegralModelOverCoeff

namespace GlobalTheory.IntegralModelOverCoeff

open Formalism.MainNotions.SumRepresentations

theorem exists_integral_model_rep : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ hc hK
  exact exists_integral_conj (A.iotaQ i) (A.iotaQ_alg i) a ρ hc hK

end GlobalTheory.IntegralModelOverCoeff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_integral_model_rep_coeffRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | exact GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | (intros; apply GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LargeO

def sysPol (n : ℕ) {E : Type} [Field E] [NumberField E] (c : HeightOneSpectrum (𝓞 E) → ℕ → ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((normV v : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c v k) * X ^ (n - k)

def BigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (Sf : Finset ℂ) : Prop :=
  ∀ c ∈ Es, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ Sf, ι.symm z ∈ K) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar l),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l))) → IsSSRep ρ →
      (∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
          IsFrob (F := D.host.E) B (normV v) σ →
          ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)).charpoly.map ι.toRingHom = sysPol D.R.nV c v) →
      ∃ Pm : GL (Fin D.R.nV) (Qbar l), ∀ g s t,
        ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)) s t ∈ K

theorem bigOk_mono {D : D7} {l : ℕ} [Fact l.Prime] {Q : Finset (PlE D.host)} {Es : Set (PlE D.host → ℕ → ℂ)}
    {ι : Qbar l ≃+* ℂ} {Sf Sf' : Finset ℂ} (h : BigOk D l Q Es ι Sf) (hs : Sf ⊆ Sf') : BigOk D l Q Es ι Sf' :=
  fun c hc K hK => h c hc K fun z hz => hK z (hs hz)

theorem bigOk_cast {D : D7} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (e : p = q) {Q : Finset (PlE D.host)}
    {Es : Set (PlE D.host → ℕ → ℂ)} {ι : Qbar p ≃+* ℂ} {Sf : Finset ℂ} (h : BigOk D p Q Es ι Sf) :
    BigOk D q Q Es (qCast e ι) Sf := by
  subst e; exact h

theorem exists_bigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (hE : Es.Finite) (hch : GlobalTheory.RowTie.ChebSplit D.nd) : ∃ Sf, BigOk D l Q Es ι Sf := by
  classical
  let Good : PlE D.host → Prop := fun v =>
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q
  let U : Set (G D.host.E D.nd.Om) := {σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}
  have hU : Dense U := GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch
  let p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun c σ =>
    if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0
  have hS := fun c => GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys l ι D.host.E D.nd.Om D.R.nV U (p c) hU
  choose Sc hSc using hS
  refine ⟨hE.toFinset.biUnion Sc, ?_⟩
  intro c hc K hK ρ hcont hss hchar
  refine hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_
  intro σ hσ
  simp only [p, dif_pos hσ]
  obtain ⟨hg, B, hB, hF⟩ := Classical.choose_spec hσ
  exact hchar _ hg B σ hB hF

theorem charpoly_pt : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.nd.l i) ∧
      v ∉ placesS D (D.nd.l i) ∧ v ∉ D.nd.Q i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
        sysPol D.R.nV (ptSys D i x) v := by
  intro D i x ρ hρ v hv B σ hB hF
  have hso : SplitOut D.nd i v := ⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩
  rw [hρ.2.2 v hso B σ hB hF, Polynomial.map_map]
  have hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i := rfl
  rw [hcomp]
  unfold heckePol sysPol

  rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hg : GenAt D (D.nd.l i) (D.nd.Q i) v k := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩
  simp only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul,
    map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

theorem model_of_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (P : GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ →
    (∀ g s t, ∃ x, A.iotaQ i x = ((P⁻¹ * ρ g * P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) →
    ∃ (r : G H.E N.Om →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ P hc hP
  let ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)) := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P := fun g => by
    simp [ρ', MulAut.conj_apply]
  have hc' : SumRepresentations.At.ContQ N i ρ' := by
    unfold SumRepresentations.At.ContQ at hc ⊢
    have e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) =
        fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) := by
      funext g; rw [hρ']; rfl
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, Pm, hr⟩ := GlobalTheory.T.exists_integral_model_rep_coeffRing N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)
  refine ⟨r, P * Pm, fun g => ?_⟩
  rw [hr g, hρ', mul_inv_rev]
  group

end GlobalTheory.LargeO
end
end
end
