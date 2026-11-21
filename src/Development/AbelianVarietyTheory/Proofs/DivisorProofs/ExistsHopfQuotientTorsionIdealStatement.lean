module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let f : B →ₐc[O] B := mulBy (R := O) (A := B) n
  let I := kerIdeal f
  let q : B →ₐ[O] B ⧸ I := Ideal.Quotient.mkₐ O I
  have hI : I.IsHopfIdeal O := by
    refine { toIsCoideal := ?_, antipode_mem := ?_ }
    · refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ }
      · intro x hx
        exact (kerIdeal_le_ker_iff f (Bialgebra.counitAlgHom O B)).2 (fun c => by simp) hx
      · intro x hx
        have hqf : ∀ c : B, q (f c) = algebraMap O (B ⧸ I) (counit (R := O) c) :=
          (kerIdeal_le_ker_iff f q).1 fun _ hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
        have hcomp : q.toLinearMap ∘ₗ (f : B →ₗ[O] B) =
            Algebra.linearMap O (B ⧸ I) ∘ₗ counit := LinearMap.ext hqf
        let Φ := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom O B)
        have hΦ : I ≤ RingHom.ker Φ := by
          refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
          have hc' : counit (R := O) c = 0 := hc
          change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
          rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply,
            ← TensorProduct.map_comp, hcomp]
          have hsplit : TensorProduct.map (Algebra.linearMap O (B ⧸ I) ∘ₗ counit)
              (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) =
              TensorProduct.map (Algebra.linearMap O (B ⧸ I))
                (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) ∘ₗ
                LinearMap.rTensor B (counit (R := O) (A := B)) := by
            rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
          rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
          simp [hc']
        exact hΦ hx
    · have hle : I ≤ I.comap (HopfAlgebra.antipodeAlgHom O B) := by
        refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
        have hc' : counit (R := O) c = 0 := hc
        change HopfAlgebra.antipode O (f c) ∈ I
        rw [← GlobalTheory.bialgHom_map_antipode]
        exact Ideal.mem_map_of_mem (f : B →ₐ[O] B) (by simp [RingHom.mem_ker, hc'])
      exact fun _ hx => hle hx
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) :=
    { comm_comp_comul := LinearMap.ext fun b => by
        obtain ⟨a, rfl⟩ := hπ b
        have h : ∀ t : B ⊗[O] B,
            TensorProduct.comm O (B ⧸ I) (B ⧸ I)
                (TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I) t) =
            TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I)
              (TensorProduct.comm O B B t) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y => simp
        change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
        rw [← CoalgHomClass.map_comp_comul_apply π a, h, comm_comul] }
  exact ⟨B ⧸ I, inferInstance, inferInstance,
    cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
