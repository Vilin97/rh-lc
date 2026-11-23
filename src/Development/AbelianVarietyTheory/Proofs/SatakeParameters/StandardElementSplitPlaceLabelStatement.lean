module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGLStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMapStatement
public import Formalism.AlgebraicWeights.IsAlgWeight
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLintStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilizeStatement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.RealUnifSplit

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]
  exact h

theorem val_sq_le {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : 𝓞 L) (hz : z ∈ s.w.asIdeal ^ 2) :
    Valued.v (s.i (z : L)) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    have ha' : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    have hb' : Valued.v (s.i (b : L)) < 1 := (s.split_mem_ideal b).1 hb
    show Valued.v (s.i ((a : L) * (b : L))) ≤ _
    rw [map_mul, map_mul]
    calc Valued.v (s.i (a : L)) * Valued.v (s.i (b : L))
        ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
          mul_le_mul' (le_exp_neg_one_of_lt ha') (le_exp_neg_one_of_lt hb')
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · intro a b ha hb
    show Valued.v (s.i ((a : L) + (b : L))) ≤ _
    rw [map_add (f := _)]
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)

end GlobalTheory.RealUnifSplit

theorem GlobalTheory.realUnif_split {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  obtain ⟨π, hπ⟩ := s.v.intValuation_exists_uniformizer
  have hv : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) π : 𝓞 L) : L)) =
      WithZero.exp (-1) := by
    rw [s.split_val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  refine ⟨algebraMap _ (𝓞 L) π, ?_, ?_, hv⟩
  · refine (s.split_mem_ideal _).2 ?_
    rw [hv]; rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro h
    have h2 := GlobalTheory.RealUnifSplit.val_sq_le s _ h
    rw [hv] at h2
    have := WithZero.exp_le_exp.1 h2
    omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  first | exact @GlobalTheory.realUnif_split | exact GlobalTheory.realUnif_split | (intros; apply GlobalTheory.realUnif_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem finPart_surjective (D : D7) : Function.Surjective (Formalism.L2.Theta.finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    exact ⟨((0, a) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (Formalism.L2.Theta.finPart D).map_add a b⟩

theorem comp_idem : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  intro D sp hF p c hπ
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  refine ⟨?_, ?_⟩
  · apply c.injective
    rw [← hπ, hπe, map_one]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := finPart_surjective D x
    obtain ⟨b, rfl⟩ := finPart_surjective D y
    have hab : p.π a = p.π b := by rw [hπ, hπ, hxy]
    have key : p.e * a = p.e * b := by rw [← p.ι_π, ← p.ι_π, hab]
    rw [← map_mul, ← map_mul, key]

end GlobalTheory.PlaceSupp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  first | exact @GlobalTheory.PlaceSupp.comp_idem | exact GlobalTheory.PlaceSupp.comp_idem | (intros; apply GlobalTheory.PlaceSupp.comp_idem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.StdEltLabel


theorem std_elt_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  intro D hF V n Ps hS hn sp ϖ hϖ k hk
  subst hn
  classical
  obtain ⟨⟨β, β', h1, h2, hm⟩, hK⟩ := id hS
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have := hϖ
    rw [Formalism.AUTREP.IsUnif, h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let g0 : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Formalism.UG.diagJ V.rank ϖ k, Matrix.diagonal (fun i => if (i : ℕ) < k then ϖ⁻¹ else 1),
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0],
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨emb, hembT, hembL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hx₀ : emb g0 ∈ Formalism.AUTREP.tSet D.host.E V.rank sp ϖ k :=
    ⟨hembT g0, 1, one_mem _, 1, one_mem _, by rw [hembL]; simp [g0]⟩
  obtain ⟨p, c, hpl, -, -, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D sp hF
  have hidem : Formalism.L2.NTheta.IsIdemAt p.e sp.w := ⟨p.split, hpl.2.2⟩
  have hprime : Formalism.IndefR.Mult.IsPrimeIdem sp.w p.e (p.e + Formalism.L2.Theta.cA D p.e) := Or.inl ⟨hidem, rfl⟩
  obtain ⟨y, hy1, hy2, hyu⟩ := GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace sp
  refine ⟨emb g0, hx₀, p.e, p.e + Formalism.L2.Theta.cA D p.e, y, hprime, hy1, hy2,
    (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V V.rank Ps hS _ _ hprime (emb g0)).2 (hembT g0), ?_⟩
  obtain ⟨sec, hs, hO', hO, hinc⟩ := GlobalTheory.T.exists_integralSection_splitPlace_componentMap D sp hF
  obtain ⟨hε, hker⟩ := GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part D sp hF p c hπ
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hφ : ∀ x, φ x = sp.proj (GlobalTheory.NJoin.tensCast hF x) := fun x => rfl
  have he : p.e * p.e = p.e := p.split.1
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis (P := sp.w) V he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hprime)
  have hee : Formalism.L2.Theta.finPart D p.e * Formalism.L2.Theta.finPart D p.e = Formalism.L2.Theta.finPart D p.e := by
    rw [← map_mul, he]
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      Formalism.L2.Theta.finPart D p.e • (X * Y) = Formalism.L2.Theta.finPart D p.e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) →
        X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hφ, hε, one_mul,
      one_mul] at this
  have hBC := mp _ _ c1
  have hCB := mp _ _ c2
  have hββ' : β.map φ * β'.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hβ'β : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]
  obtain ⟨N, hNdef⟩ : ∃ N : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)),
      (N : Matrix (Fin V.rank) (Fin V.rank) _) = β'.map φ * B.map φ :=
    ⟨⟨β'.map φ * B.map φ, C.map φ * β.map φ,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ), hBC, Matrix.one_mul, hβ'β],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map φ), hββ', Matrix.one_mul, hCB]⟩, rfl⟩
  have hlat := GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer hF Ps sp β β' h1 h2 hm hK (Formalism.L2.Theta.finPart D p.e) sec B hs hO' hO hε b1 b2
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul _ sp.v V.rank N (by rw [hNdef]; exact hlat) (Formalism.UG.diagJ V.rank ϖ k)
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL _ sp.v V.rank k ϖ (sp.i (y : D.host.E)) hϖ hyu
  rw [GlobalTheory.DivDual.divAt_iff]
  refine ⟨by simp [hk], ?_⟩
  have hk₂' : T * k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) := mul_mem hT hk₂
  refine GlobalTheory.SphLabelOps.dv_of_cartan (OK := Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) φ sec hs hε hker
    (fun x hx => hO x hx) (fun t ht => hO' t ht) b1 b2
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂') (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂')) ?_
  have hdiag : (Matrix.diagonal fun i : Fin V.rank => φ (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D
      ((y : D.host.E) ^ ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))))) =
      Matrix.diagonal (fun i : Fin V.rank => sp.i (y : D.host.E) ^
        ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0)) := by
    congr 1; funext i; rw [hφ, hinc, map_zpow₀]
  have hA : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g0))).map φ =
      β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ := by
    rw [hm, Matrix.map_mul, Matrix.map_mul]
    congr 2
    have e2 : ((emb g0).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map sp.proj =
        Formalism.UG.diagJ V.rank ϖ k := congrArg Units.val (hembL g0)
    rw [← e2, Matrix.map_map]
    congr 1
    funext x
    simp [φ]
  have hBN : B.map φ = β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
    rw [hNdef, ← Matrix.mul_assoc, hββ', Matrix.one_mul]
  have hNN : (N : Matrix (Fin V.rank) (Fin V.rank) _) *
      (N⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hdiag, hA, hBN]
  calc β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ * (β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _))
      = β.map φ * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β'.map φ), hβ'β, Matrix.one_mul]
    _ = β.map φ * ((N : Matrix (Fin V.rank) (Fin V.rank) _) *
          ((N⁻¹).val *
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _))) := by
        have e3 : (N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)) =
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNN, Matrix.one_mul]
        rw [e3, Matrix.mul_assoc]
    _ = _ := by
        rw [hkk, hTe]
        simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.StdEltLabel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.standardElement_splitPlace_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  first | exact @GlobalTheory.StdEltLabel.std_elt_label | exact GlobalTheory.StdEltLabel.std_elt_label | (intros; apply GlobalTheory.StdEltLabel.std_elt_label <;> assumption)
end
end
