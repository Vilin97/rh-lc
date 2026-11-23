module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerProjectionMaximalThetaSubspace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolKernelEqThetaSubspaceOfMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationMatchLieDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStabStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolynomialMatchingInduction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalFixesPureVacuumVectors
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RankPolarizationPiLeAleph0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubgroupOfKerDerivation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceEqKerProjDerivationOfSquare
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceKernelMaximal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchOnto

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Φ' ∈ algD G.M' B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hM Φ hΦ
  classical
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hφ hfin hg using fun i => (g i).2
  have hfin' : ∀ i, {v | ¬ φ i v = G.M.vac v}.Finite := fun i => Filter.eventually_cofinite.1 (hfin i)
  set T : Finset (Pl F) := X.T ∪ Finset.univ.biUnion (fun i => (hfin' i).toFinset) with hT
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := by
    intro i v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin' i).mem_toFinset.2 h⟩))
  have hreal : ∀ i, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p (c i • f i) := by
    intro i
    have : R.p (c i • f i) ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose f' hf' hf'eq using hreal
  have hloc : ∀ i v, ∃ y ∈ GlobalTheory.WeilM.SB _, Rf.p' v y = Rf.p v (φ i v) := by
    intro i v
    have : Rf.p v (φ i v) ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose φ₀ hφ₀ hφ₀eq using hloc
  let φ' : Fin n → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun i v => if v ∈ T then φ₀ i v else G.M'.vac v
  have hvac' : ∀ v, G.M'.vac v ∈ GlobalTheory.WeilM.SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  have hφ'SB : ∀ i v, φ' i v ∈ GlobalTheory.WeilM.SB _ := by
    intro i v
    by_cases hv : v ∈ T
    · simpa only [φ', ite_eq_left hv] using hφ₀ i v
    · simpa only [φ', ite_eq_right hv] using hvac' v
  have hφ'out : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := by
    intro i v hv; simp only [φ', ite_eq_right hv]
  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) = c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) := by
    intro i
    rw [hg i]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' i) (φ' i), ?_, T, Finset.subset_union_left, n, n, fun i => c i • f i, φ, f', φ', ?_, ?_, ?_, rfl, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, φ' i, hf' i, hφ'SB i, ?_, rfl⟩
    exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hφ'out i v h))
  · exact fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hout i⟩
  · exact fun i => ⟨hf' i, hφ'SB i, hφ'out i⟩
  · exact Finset.sum_congr rfl fun i _ => (hpure i).symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf'eq i]
    apply congrArg (fun z => R.p (c i • f i) ⊗ₜ[ℂ] z)
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext v
    simp only [φ', ite_eq_left v.property]
    exact (hφ₀eq i v).symm

end GlobalTheory.SquareAgree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOnStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.InfKill.smul_mat_kapX_sub_one | exact GlobalTheory.InfKill.smul_mat_kapX_sub_one | (intros; apply GlobalTheory.InfKill.smul_mat_kapX_sub_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem conjU_one_eq {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationMatchSquareKappa

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree
theorem polarization_match_square_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ g ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1, kapX X e hO.JX g) ΦD) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1, kapX X e hO.JX g) Φ₀D) := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf hM Pi rf rl p p' _ g hg ΦD _ Φ₀D _ hPM
  rw [conjU_one_eq, conjU_one_eq]
  have hinf := GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨T₀, hXT, hOn⟩ := hPM
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T₀ ∪ S₀)
  have ext : ∀ U : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (T₀ ∪ U) ΦD Φ₀D := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.union_empty]; exact hOn
    | insert v U hv ih =>
      rw [Finset.union_insert]
      by_cases hvX : v ∈ Xc.T
      · rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ (hXT hvX))]
        exact ih
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert _ _ _ Bs _ _ Γ Xc R Rf v (hM.fin.sph v hvX).1 _ _ _ ih
  have hOnS : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S ΦD Φ₀D := by
    have := ext S
    rwa [Finset.union_eq_right.2 (Finset.union_subset_left hTS)] at this
  have hU := hS₀ S (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have hOnK : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, k) ΦD) (om' (1, k) Φ₀D) := by
    obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hOnS
    refine ⟨m, m', f, φ, f', φ', hφ, hφ', ?_, ?_, hsum⟩

    · rw [hΦ, map_sum]
      exact Finset.sum_congr rfl fun i _ => hU.1 (f i) (φ i) (hφ i).2.1 (hφ i).2.2

    · rw [hΦ', map_sum]
      exact Finset.sum_congr rfl fun j _ => hU.2 (f' j) (φ' j) (hφ' j).2.1 (hφ' j).2.2
  have split : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om (1, x * y) Φ = om (1, x) (om (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om' (1, x * y) Φ = om' (1, x) (om' (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, (l'.map Prod.snd).prod * k) ΦD)
        (om' (1, (l'.map Prod.snd).prod * k) Φ₀D) := by
    intro l'
    induction l' with
    | nil => intro _; simpa using hOnK
    | cons x l' ih =>
      intro hx
      have h1 := hx x List.mem_cons_self
      have h2 := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, mul_assoc]
      rw [split, split']
      exact _root_.GlobalTheory.T.polynomial_matching_induction hP _ _ _ Bs _ _ Γ Xc om om' R Rf hM S x.1 h1.1 x.2 h1.2 _ _ h2
  rw [hprod]
  exact ⟨S, hXT.trans (Finset.subset_union_left.trans hTS), key l hl⟩
end GlobalTheory.SquareAgree
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelMatchOnOppositeParabolic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree
theorem theta_kernel_match_on_parabolic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := _root_.GlobalTheory.T.theta_subspace_kernel_maximal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := _root_.GlobalTheory.T.thetaSubspace_contains_polKernel hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (_root_.UpperTheory.Lit.HoweDuality.twisted_theta_kernel_condition hR hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂
theorem theta_kernel_match_on_opposite_parabolic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, _root_.UpperTheory.Lit.HoweDuality.twisted_theta_jet_condition hR hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (_root_.GlobalTheory.T.thetaKernel_projection_isMax hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0
theorem theta_kernels_agree_up_to_scalar : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  intro hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hTD.base.std
  have dA := GlobalTheory.SquareAgree.isDatum_linear Γ.M ψ hstd cA
  have dB := GlobalTheory.SquareAgree.isDatum_linear Γ.M' ψ hstd cB
  have lin := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hR.fin
  let G : Set (Pi × Pi) := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ₀ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      ∃ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ ∧ IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D ∧ x = (p Φ, p' Φ₀)}
  have G0 : (0 : Pi × Pi) ∈ G :=
    ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, 0, zero_mem _, dA.1, dB.1, lin.1, Prod.ext (map_zero p).symm (map_zero p').symm⟩
  have Glin : ∀ x ∈ G, ∀ y ∈ G, ∀ c : ℂ, x + c • y ∈ G := by
    rintro _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩ _ ⟨Ψ, hΨ, Ψ₀, hΨ₀, ΨD, hΨD, Ψ₀D, hΨ₀D, k1, k2, k3, rfl⟩ c
    exact ⟨Φ + c • Ψ, add_mem hΦ (Submodule.smul_mem _ c hΨ), Φ₀ + c • Ψ₀, add_mem hΦ₀ (Submodule.smul_mem _ c hΨ₀),
      ΦD + c • ΨD, add_mem hΦD (Submodule.smul_mem _ c hΨD), Φ₀D + c • Ψ₀D, add_mem hΦ₀D (Submodule.smul_mem _ c hΨ₀D),
      dA.2 _ _ _ _ c h1 k1, dB.2 _ _ _ _ c h2 k2, lin.2 _ _ _ _ c h3 k3, by ext <;> simp⟩
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := G
      add_mem' := fun {x y} hx hy => by simpa using Glin x hx y hy 1
      zero_mem' := G0
      smul_mem' := fun c x hx => by simpa using Glin 0 G0 x hx c }
  have stf : ∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S := by
    rintro g hg _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    have a1 := hM.mapA.stabX.1 g hg Φ hΦ
    have b1 := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ a1
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ b1
    have e1 := GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hΨ (hO.weilA ΦD Φ h1 1 g)
    have e2 := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hΨ₀ (hO.weilB Φ₀D Φ₀ h2 1 g)
    refine ⟨_, a1, _, b1, ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀, ?_, ?_⟩
    · rw [e1, e2]
      exact _root_.GlobalTheory.SquareAgree.polarization_match_square_kappa hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM g hg ΦD hΦD Φ₀D hΦ₀D h3
    · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ₀ hΦ₀]
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S := by
    rintro τ Y hY _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    obtain ⟨Φ', hΦ', hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
    obtain ⟨Φ₀', hΦ₀', hd₀⟩ := hM.mapB.stabX.2 τ Y hY Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ hΦ'
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ hΦ₀'
    refine ⟨Φ', hΦ', Φ₀', hΦ₀', ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀,
      _root_.GlobalTheory.SquareAgree.LieEq.polarization_match_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM τ Y hY Φ hΦ Φ' hΦ' Φ₀ hΦ₀ Φ₀' hΦ₀' hd hd₀ ΦD hΦD ΨD hΨD Φ₀D hΦ₀D Ψ₀D hΨ₀D h1 hΨ h2 hΨ₀ h3, ?_⟩
    rw [hM.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hM.mapB.eql τ Y hY Φ₀ hΦ₀ Φ₀' hΦ₀' hd₀]
  have k1 : ∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0 := by
    rintro x ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, h0⟩ := hx
    have m0 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).2 m1
  have k2 : ∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0 := by
    rintro y ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hy⟩
    simp only [Prod.mk.injEq] at hy
    obtain ⟨h0, rfl⟩ := hy
    have m0 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).2 m1
  have on : ∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S := by
    intro x
    have hx : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
    obtain ⟨Φ, hΦ, rfl⟩ := hx
    obtain ⟨ΦD, hΦD, h1⟩ := hO.algA Φ hΦ
    obtain ⟨Φ₀D, hΦ₀D, h3⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
    obtain ⟨Φ₀, hΦ₀, h2⟩ := hO.algB' Φ₀D hΦ₀D
    exact ⟨p' Φ₀, Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SquareAgree.eq_smul_of_stable_graph D X Pi rf rl hM.irred (_root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM) S stf stl k1 k2 on
  refine ⟨c, hc0, ?_⟩
  intro Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
  obtain ⟨ΦD', hΦD', h1⟩ := hO.algA Φ hΦ
  have hΦD : ΦD ∈ algD Γ.M Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hD h1) ▸ hΦD'
  obtain ⟨Φ₀D', hΦ₀D', h2⟩ := hO.algB Φ₀ hΦ₀
  have hΦ₀D : Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hD₀ h2) ▸ hΦ₀D'
  obtain ⟨Φ₁D, hΦ₁D, m1⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
  obtain ⟨Φ₁, hΦ₁, h4⟩ := hO.algB' Φ₁D hΦ₁D
  have hy := hc (p Φ) (p' Φ₁) ⟨Φ, hΦ, Φ₁, hΦ₁, ΦD, hΦD, Φ₁D, hΦ₁D, hD, h4, m1, rfl⟩
  have h5 := dB.2 _ _ _ _ (-c) h4 hD₀
  have hz : p' (Φ₁ + (-c) • Φ₀) = 0 := by rw [map_add (f := _), map_smul, hy, hp, neg_smul, add_neg_cancel]
  have m2 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM _ (add_mem hΦ₁ (Submodule.smul_mem _ _ hΦ₀)) _
    (add_mem hΦ₁D (Submodule.smul_mem _ _ hΦ₀D)) h5).1 hz
  have m3 := lin.2 _ _ _ _ (-1) m1 m2
  have e3 : Φ₁D + (-1 : ℂ) • (Φ₁D + (-c) • Φ₀D) = c • Φ₀D := by module
  rw [smul_zero, add_zero, e3] at m3
  exact GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hTD _ _ m3 (Submodule.smul_mem _ c hSo)
end GlobalTheory.SquareAgree
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  first | exact @_root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar | exact _root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar | (intros; apply _root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar <;> assumption)
end
end
end
