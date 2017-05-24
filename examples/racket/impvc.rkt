(define (format-result r)
  (match r
    ((Unknown) "Unknown solution")
    ((Uninhabited) "Uninhabited")
    ((Solution s) (format "Solution ~a" s))))

(displayln "Imp VC application")

(displayln (format-result (@ impVCRosette env0 p0 s0 q0)))

