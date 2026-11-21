module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPWMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilDatumSplittingCharacters
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.LatK

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

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
  have hex := (open Formalism.IndefR.DatumF Formalism.IndefR.LiftF GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF PositivityTheory.ThKW.Eta in
    show ∃ η : (AF F ⊗[F] E)ˣ →* Circle,
      IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) ∧ UnramInert σ η from by
      haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
      obtain ⟨η, h1, h2, h3⟩ := _root_.GlobalTheory.EtaCMType.exists_eta_cmType_k F E σ B hB
      obtain ⟨N, hN, hk⟩ := _root_.PositivityTheory.ThKW.Eta.key_k hB h1.1 h2
      obtain ⟨ν, hV, hU⟩ := exists_ext _ _ η hk
      have hW : ∀ z ∈ WE F E N, ν z = 1 := fun z hz => hV z (Subgroup.mem_sup_right hz)
      have hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ) := by
        have ho := CE_isOpen F E N hN
        have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
          Units.continuous_val.sub continuous_const
        have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
          Units.continuous_coe_inv.sub continuous_const
        exact (ho.preimage hcv).inter (ho.preimage hci)
      have hν : Continuous ν := by
        refine continuous_of_continuousAt_one _ ?_
        unfold ContinuousAt
        rw [map_one]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
        exact (hW z hz).symm
      refine ⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => ?_⟩, ⟨h2.1, fun e he a => ?_⟩, fun z hz => ?_, fun x a b c d => ?_⟩
      · change η _ * (ν _)⁻¹ = 1
        rw [h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]
      · change η _ * (ν _)⁻¹ = _
        rw [h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]
      · change ((η z * (ν z)⁻¹ : Circle) : ℂ) = _
        have : z ∈ WE F E N := by
          refine ⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ ?_⟩
          intro u hu
          have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
              -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
            rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
          rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
        rw [hW z this, inv_one, mul_one]
        exact h3 z hz
      · change η _ * (ν _)⁻¹ = 1
        have hx : x ∈ UI σ := by
          refine ⟨?_, b, mem_SE_of_fin c, mem_SE_of_fin d⟩
          show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E
          rw [← sub_eq_zero, ← mul_sub_one]
          refine adele_tensor_ext _ ?_ ?_
          · rw [map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero]
          · rw [map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]
        rw [hU x hx, mul_inv_cancel])
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := hex
  obtain ⟨Λ, hΛ1, hΛ2⟩ := hLat
  have hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ := _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀
  obtain ⟨w, lam, Om, hO⟩ := _root_.UpperTheory.TP.W.latK F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc
  have hK := _root_.UpperTheory.TP.W.kapEx
  have hE := _root_.UpperTheory.TP.W.etaProdK
  have hI := _root_.UpperTheory.TP.W.idxSign _root_.UpperTheory.TP.W.cardDet _root_.UpperTheory.TP.W.idxHalf
  have hex2 := (open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.WeilPartsF PositivityTheory.ThKW in
    show ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω from by
      obtain ⟨θ, hθ⟩ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).2.1
      obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.exists_chart_archimedean_family F E σ B hB θ hθ
      have C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι := ⟨hB, hS, hT, hξ, hξσ, hθ, hι⟩
      obtain ⟨κ, hκ⟩ := hK F E σ hB.cm lam hO.good
      obtain ⟨ε, hε, hprod⟩ := hE F E σ B hB.cm hB.unram η hη1 hη2 hη3 hη4 lam hO.good κ hκ
      obtain ⟨of, hf, hof⟩ := _root_.UpperTheory.TP.W.existsFinK_k hI C hΛ1 hO hη1 hη2 hκ hε
      obtain ⟨oi, hi, hvac⟩ := _root_.PositivityTheory.ThKW.exists_inf_k C
      have P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om (η * κ) (η ^ nS) (η ^ nT) ε of oi := ⟨_root_.UpperTheory.TP.W.resEta_mul hη2 hκ, hε, hprod, hf, hof, hi, hvac⟩
      have hcomm := _root_.PositivityTheory.ThKW.fin_inf_comm_k C hO (fun p => ⟨_, hof p⟩) hi
      refine _root_.PositivityTheory.ThKW.datum_of_aut_k C hΛ1 hO hη1 hη2 hf (fun p => ⟨_, hof p⟩) hi fun γ hγ γ' hγ' f hf' => ?_
      have := _root_.PositivityTheory.ThKW.rat_gen_k C (fun p => IsScalarF B ξ₀ of oi p 1)
        (fun p q _ _ q1 q2 a b => mul_one (1 : ℂ) ▸ a.mul_k C hi hcomm b q1 q2)
        (fun p s p1 p2 hs hcm => _root_.UpperTheory.TP.W.isScalar_one_of_commK_k C hΛ1 hΛ2 hO P hs p1 p2 hcm) (γ, γ') hγ hγ' f hf'
      rw [this, one_smul]
      show f (actOF σ JS JT γ⁻¹ γ'⁻¹ 0) = f 0
      rw [actOF, Matrix.mul_zero, Matrix.zero_mul])
  obtain ⟨om, hom⟩ := hex2
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.T.weil_datum_splitting_characters F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ _ _ ((η ^ nS)⁻¹ * χS) ((η ^ nT)⁻¹ * χT) om hom
    (isHeckeCharF_div_pow hcS hη1 _) (isHeckeCharF_div_pow hcT hη1 _)
    (resEtaF_div_pow rS hη2) (resEtaF_div_pow rT hη2)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩
end PositivityTheory.ThKW.S
end
