module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacuaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTopStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.InertOfKept
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBS
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.CardDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.ContinuousOfWE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.EtaProdK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IdxHalf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IdxSign
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPWDatumK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.LatK

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

theorem UpperTheory.TP.W.latK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatB.sg_sg hB.cm
  obtain ⟨w, hw⟩ := LatB.exists_w hB.cm hB.unram
  obtain ⟨lam, hlam⟩ := UpperTheory.TP.W.normK F E σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (GlobalTheory.FinLatF.actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, fun x => ?_,
    LatC.near hg, LatC.near' hg, fun e he a ha => ?_⟩
  · obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
    refine ⟨2 * M, by omega, fun l hl => ?_⟩
    have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
      rw [H.nsmul_right, ← H.nsmul_left]
      exact H.iso hA hx hl
    rw [mul_smul, LatC.symplOHF_two]
    exact h3
  · obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
    exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPWMain

section

@[expose] public section



section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
theorem UpperTheory.TP.W.datumK_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  _root_.UpperTheory.TP.W.datumK_of_k UpperTheory.TP.W.kapEx UpperTheory.TP.W.etaProdK (UpperTheory.TP.W.idxSign UpperTheory.TP.W.cardDet UpperTheory.TP.W.idxHalf)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilDatumOFTwistK

section

@[expose] public section



section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
theorem exists_weilDatumOF_twist_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ χS χT νS νT om ho hνS hνT rS rT
  have hcm := hB.cm
  have hun := hB.unram
  obtain ⟨a, aval, arat, acont⟩ := exists_muF (σ := σ) hcm hun hS.2 νT⁻¹ (heckeF_inv hνT)
    (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rT, inv_one])
  obtain ⟨b, bval, brat, bcont⟩ := exists_muF (σ := σ) hcm hun hT.2 νS hνS (triv_of_resEtaF rS)
  let om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ) :=
    { toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]
        congr 1
        ring }
  have happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsRootF σ JS g x → IsRootF σ JT h y →
      ((a g * b h : Circle) : ℂ) = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval g x hx, bval h y hy, MonoidHom.inv_apply]
  refine ⟨om', ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rS,
    resEtaF_mul ho.resT rT, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p f hf
    rw [happ]
    exact thetaOF_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ]
    change ((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0
    rw [arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact (continuous_subtype_val.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul
      (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (root_of_detAt hS.2 he g hg x hx) (root_of_detAt hT.2 he h hh y hy)]
    simp only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
end GlobalTheory.WeilTwistF
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilDatumSplittingCharacters

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.weil_datum_splitting_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @_root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | exact _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | (intros; apply _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSDat

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace PositivityTheory.ThKW.S
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_isWeilDatumOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∃ ω, Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ hLat χS χT hcS hcT rS rT
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := _root_.PositivityTheory.ThKW.exists_eta_k F E σ B hB
  obtain ⟨Λ, hΛ1, hΛ2⟩ := hLat
  have hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ := _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀
  obtain ⟨w, lam, Om, hO⟩ := _root_.UpperTheory.TP.W.latK F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc
  obtain ⟨om, hom⟩ := _root_.UpperTheory.TP.W.datumK_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc w lam Om hO η hη1 hη2 hη3 hη4
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.T.weil_datum_splitting_characters F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ _ _ ((η ^ nS)⁻¹ * χS) ((η ^ nT)⁻¹ * χT) om hom
    (isHeckeCharF_div_pow hcS hη1 _) (isHeckeCharF_div_pow hcT hη1 _)
    (resEtaF_div_pow rS hη2) (resEtaF_div_pow rT hη2)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩
end PositivityTheory.ThKW.S
end
end
end
