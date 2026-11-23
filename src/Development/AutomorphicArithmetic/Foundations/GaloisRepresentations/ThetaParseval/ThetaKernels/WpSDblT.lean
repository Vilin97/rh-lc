module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilPairGlobalIntertwiner
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationHermitianPair
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairContinuous
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairEquivariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairSmooth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairUnitary
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSDat
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaTrCoDblBoxFunK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.DblThetaProd
theorem thetaTr_coDbl_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only
  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]
end GlobalTheory.DblThetaProd
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrangianDarbouxThetaModel

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.lagrangian_darboux_theta_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @_root_.GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun_k | exact _root_.GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun_k | (intros; apply _root_.GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RestrictBoxFunK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrict
theorem restrict_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat om hom
    ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let h : Formalism.IndefR.DatumF.GAF σ JT := ⟨g.1, GlobalTheory.TransportF.mem_HR_target hA g⟩
  let hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := ⟨gd.1, GlobalTheory.TransportF.mem_HR_target rfl gd⟩
  have hh : Formalism.IndefR.DatumF.mtF σ JT h = g.1.1 := rfl
  have hhd : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd = gd.1.1 := rfl
  have h1 : Formalism.IndefR.DatumF.mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    show (Formalism.IndefR.DatumF.matHomF σ JS 1).1 = _
    rw [map_one, inv_one]
    first | rfl | simp | exact Matrix.transpose_one.symm
  have hdm : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) := by
    rw [hhd, hgd, hh]
  have t1 := hom g 1 1 h hh h1 φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ hφ₁ φ₂ hφ₂
  have hΦ' := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ t1.1 φ₂ hφ₂
  have t2 := homp gd 1 1 hd hhd h1 _ hΦ
  have hφ₂' := GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection F κ φ₂ hφ₂
  let τ := Fintype.equivFin κ
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hA hB', co.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      GlobalTheory.TransportF.numCoordF co τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  have thf : ∀ Φ ∈ schA F κ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := fun Φ hΦ => by
    rw [GlobalTheory.TransportF.thetaTr_eqF co τ]
    exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (GlobalTheory.TransportF.numCoordF co τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  have key := t2.2.trans ((congrArg (ωd (1, hd)) (_root_.GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((_root_.GlobalTheory.T.weil_pair_global_intertwiner F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT ω hω ωd hωd h hd hdm _ _ (thf φ₁ hφ₁) (thf _ hφ₂')).trans
      ((congrArg (fun f => GlobalTheory.DblTargetDelta.deltaT f
        (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (_root_.GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co _ t1.1 φ₂ hφ₂).symm)))
  let τ' := Fintype.equivFin (κ ⊕ κ)
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' ((omp (gd, 1)) (boxFun φ₁ φ₂))] at key
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' (boxFun (om (g, 1) φ₁) φ₂)] at key
  have h2 := GlobalTheory.TransportF.thV_injOn hR hψ (GlobalTheory.TransportF.comp_mem_schA τ' t2.1) (GlobalTheory.TransportF.comp_mem_schA τ' hΦ')
    ((GlobalTheory.TransportF.numCoordF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ').surjective.injective_comp_right key)
  funext x
  have hx : (x ∘ τ'.symm) ∘ τ' = x := by
    funext i
    simp
  erw [← hx]
  exact congrFun h2 (x ∘ τ'.symm)
end GlobalTheory.DblTargetRestrict
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledWeilApplyBoxFunEqBoxFunLeft

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.doubled_weil_apply_boxFun_eq_boxFun_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @_root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k | exact _root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k | (intros; apply _root_.GlobalTheory.DblTargetRestrict.restrict_boxFun_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSDblT

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace PositivityTheory.ThKW.S
theorem exists_dbl_target_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ hLat χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  have hJTd := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hJT
  have h1 := GlobalTheory.WeilSchrodinger.DblTargetF.isHeckeCharF_one (F := F) (E := E)
  have r1 := GlobalTheory.WeilSchrodinger.DblTargetF.resEtaF_one_dbl h2 rT
  obtain ⟨ωd, hωd⟩ := _root_.PositivityTheory.ThKW.S.exists_isWeilDatumOF_k F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ (PositivityTheory.ThKW.LatH.dblT hLat) χS 1 hS h1 rS r1
  have hrat' := GlobalTheory.WeilSchrodinger.DblTargetF.coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := _root_.GlobalTheory.T.weil_representation_hermitian_pair F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat'
  have k2 := _root_.GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k3 := _root_.GlobalTheory.T.weil_representation_pair_smooth F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k4 := _root_.GlobalTheory.T.weil_representation_pair_unitary F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k5 := _root_.GlobalTheory.T.weil_representation_pair_equivariant F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have hsp : IsUSplitting (adeleClass F) B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) (actAB (cA σ)) omp :=
    ⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩
  have hsg := _root_.GlobalTheory.T.splitting_character_restricted_eta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS hS rS JB ξ hBm (κ ⊕ κ)
    (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := GlobalTheory.WeilSchrodinger.DblTarget.isDblCoord_transD co
  have t2 : IsLagr (cA σ) (dbl (incM F JA)) (diagCols (Fin nT)) := isLagr_diagCols _ _
  have t4 := GlobalTheory.WeilSchrodinger.DblTarget.isUSplitting_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA)
    (GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp)
  have t5 := GlobalTheory.WeilSchrodinger.DblTarget.siegelRule_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := _root_.GlobalTheory.T.doubled_weil_apply_boxFun_eq_boxFun_left F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
    ωd hωd omp hmp g (GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl hA gd)
    (by rw [GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key
end PositivityTheory.ThKW.S
end
end
end
end
