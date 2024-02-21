theorem ft_valid : ∀ (x : RubiksSuperType), FaceTurn x → x ∈ ValidCube :=
  fun x hx ↦
    FaceTurn.casesOn (motive := fun a t ↦ x = a → HEq hx t → x ∈ ValidCube) hx
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.U → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 1, 2, 3], orient := 0 },
                            { permute := cyclePieces [0, 1, 2, 3], orient := 0 }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.D → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [4, 5, 6, 7], orient := 0 },
                            { permute := cyclePieces [4, 5, 6, 7], orient := 0 }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.R → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [1, 6, 5, 2], orient := Orient 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)] },
                            { permute := cyclePieces [1, 9, 5, 10], orient := 0 }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.L → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 3, 4, 7], orient := Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)] },
                            { permute := cyclePieces [3, 11, 7, 8], orient := 0 }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.F → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [2, 5, 4, 3], orient := Orient 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)] },
                            { permute := cyclePieces [2, 10, 4, 11],
                              orient := Orient 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)] }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.B → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 7, 6, 1], orient := Orient 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)] },
                            { permute := cyclePieces [0, 8, 6, 9],
                              orient := Orient 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)] }).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.U2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [0, 1, 2, 3], orient := 0 },
                              { permute := cyclePieces [0, 1, 2, 3], orient := 0 }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.D2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [4, 5, 6, 7], orient := 0 },
                              { permute := cyclePieces [4, 5, 6, 7], orient := 0 }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.R2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [1, 6, 5, 2], orient := Orient 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)] },
                              { permute := cyclePieces [1, 9, 5, 10], orient := 0 }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.L2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [0, 3, 4, 7], orient := Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)] },
                              { permute := cyclePieces [3, 11, 7, 8], orient := 0 }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.F2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [2, 5, 4, 3], orient := Orient 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)] },
                              { permute := cyclePieces [2, 10, 4, 11],
                                orient := Orient 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)] }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.B2 → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      (({ permute := cyclePieces [0, 7, 6, 1], orient := Orient 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)] },
                              { permute := cyclePieces [0, 8, 6, 9],
                                orient := Orient 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)] }) ^
                            2).1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.U' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 1, 2, 3], orient := 0 },
                              { permute := cyclePieces [0, 1, 2, 3], orient := 0 })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.D' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [4, 5, 6, 7], orient := 0 },
                              { permute := cyclePieces [4, 5, 6, 7], orient := 0 })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.R' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [1, 6, 5, 2], orient := Orient 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)] },
                              { permute := cyclePieces [1, 9, 5, 10], orient := 0 })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.L' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 3, 4, 7], orient := Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)] },
                              { permute := cyclePieces [3, 11, 7, 8], orient := 0 })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.F' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [2, 5, 4, 3], orient := Orient 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)] },
                              { permute := cyclePieces [2, 10, 4, 11],
                                orient := Orient 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)] })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (fun h ↦
        Eq.ndrec (motive := fun x ↦ ∀ (hx : FaceTurn x), HEq hx FaceTurn.B' → x ∈ ValidCube)
          (fun hx h ↦
            id
              {
                left :=
                  Eq.refl
                    (sign
                      ({ permute := cyclePieces [0, 7, 6, 1], orient := Orient 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)] },
                              { permute := cyclePieces [0, 8, 6, 9],
                                orient := Orient 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)] })⁻¹.1.permute),
                right := Prod.mk_eq_zero.mp rfl })
          h.symm hx)
      (Eq.refl x) (HEq.refl hx)


  #print ft_valid
