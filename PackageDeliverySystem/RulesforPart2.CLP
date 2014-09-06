

;Rules to calculate the shortest distance between all the cities present in the map
;Each combination is considered their and shortest route is calculated.
;Shortest route from a city to itself is given as zero.
;As the truck needs to pick up packages in between route of two cities the path between two cities is also noted into a slot.

(defrule direct-shortest-distance0 
	(declare (salience 2))
	(city (city_name ?start_city)
		(connected_cities $?))
=>
	(assert (shortest_path (city1 ?start_city)
				(city2 ?start_city)
				(time 0))))

(defrule direct-shortest-distance 
	(declare (salience 2))
	(city (city_name ?start_city)
		(connected_cities $? ?end_city ?time $?))
	(city (city_name ?end_city)
		(connected_cities $?))
	(not (shortest_path (city1 ?start_city)
			    (city2 ?end_city)))
=>
	(assert (shortest_path (city1 ?start_city)
				(city2 ?end_city)
				(time ?time))))


(defrule indirect-shortest-distance1
	(declare (salience 1))
	(city (city_name ?end_city)
		(connected_cities $?))
	(city (city_name ?start_city)
		(connected_cities $?))
	(shortest_path (city1 ?start_city)
			     (city2 ?city1&:(neq ?city1 ?end_city))
			    (time ?t1)
			    (via $?v))
	(shortest_path (city1 ?city1)
			(city2 ?city2&:(eq ?city2 ?end_city))
			(time ?t2))
	(not (shortest_path (city1 ?start_city)
			    (city2 ?end_city)))
=>
	(assert (shortest_path (city1 ?start_city)
				(city2 ?city2)
				(time (+ ?t2 ?t1))
				(via $?v ?city1))))

(defrule indirect-shortest-distance2
	(declare (salience 1))
	(city (city_name ?end_city)
		(connected_cities $?))
	(city (city_name ?start_city)
		(connected_cities $?))
	(shortest_path (city1 ?start_city)
			     (city2 ?city1&:(neq ?city1 ?end_city))
			    (time ?t1)
			    (via $?v))
	(shortest_path (city1 ?city1)
			(city2 ?city2&:(eq ?city2 ?end_city))
			(time ?t2))
	(shortest_path (city1 ?start_city)
			    (city2 ?end_city))
	?new <- (shortest_path (city1 ?start_city)
			    (city2 ?city2&:(eq ?city2 ?end_city))
			    (time ?t3&:(> ?t3 (+ ?t2 ?t1)))
			    (via $?v1))
=>
	(modify ?new (city1 ?start_city)
		     (city2 ?city2)
		     (time (+ ?t2 ?t1))
	             (via $?v ?city1)))






;Rules handling all the situations of the Delivery system.

(defrule update-time    ;defrule to maintain the program clock 
			;untill there is no package whose arrival time is not equal to clock 
			;and there is no package whose arrival time is less than updating time
			;also, there must be no truck whose reach time is less than updating time.
 ?cur-time <- (current-time ?time) 
 (package (arrival_time ?new-time&:(neq ?time ?new-time))
	  (status "arrived")) 
 (not (package (arrival_time ?x&:(< ?x ?new-time))
		(status "arrived"))) 
 (not (truck (reached_time ?r_time&:(< ?r_time ?time))
	     (current_action "going to pick a package"|"in route to deliver a package")))
 => 
 (retract ?cur-time) 	;retract the existing time and asserting the new one
 (assert (current-time ?new-time)) )

;There are 3 situations which may happen when a package is arrived 
;1. A truck from its current city can pick it up, when there is no other idle truck which can reach the package depart city earlier.
;2. If there is a truck which can reach package depart city earlier, then that truck picks up the package.
;3. If there is no idle truck available to pick an arrived package it enters the queue and waits for an idle truck to pick it up.


(defrule truck-to-load-package				;defrule to manage the situation where a package has been arrived and an idle truck 
											;with lower number and available space more than package size which reaches depart 
											;city first among others leaves its current city to package depart city to pick it up 
	(current-time ?time) 
	?pack <- (package (package_no ?pnum)
		 	(arrival_time ?time)
	 	 	(size_of_package ?package_size)
		 	(depart_city ?start_city)
			(deliver_city ?end_city)
		 	(status "arrived")
		 	(exp_delivery_time ?package_delivery_time)) 
	(not (package (package_no ?pnum1&:(< ?pnum1 ?pnum))		;condition to check there is no package whose arrival time is less than current time
		      (arrival_time ?atime&:(< ?atime ?time))
	 	 	(size_of_package ?package_size1)
		 	(depart_city ?start_city)
			(deliver_city ?end_city1)
		 	(status "arrived")
		 	(exp_delivery_time ?package_delivery_time1)) )

	?truck <- (truck (truck_no ?truck_no)				;choosing the truck which picks up the package early and no truck of lower number with 
			 	(destination_city $?d)					;same charateristics exists
	       		 	(current_city ?truck_city)
			 	(current_action "idle")
			 	(busy_time ?b_time)
			 	(waiting_time ?w_time)
			 	(reached_time ?r_time)
			 	(non_del_time ?ndeltime)
				(numofpack $?nop)
	       		 	(Available_space ?truck_space&:(>= ?truck_space ?package_size)))		
			 (shortest_path (city1 ?truck_city)
					(city2 ?start_city)
					(time ?s_path))	
	(not (and (truck (truck_no ?truck_num1&:(< ?truck_num1 ?truck_no))	;there must be no truck in same place whose number is less than the one picking it up
	            	 (current_city ?truck_city)				
		    	 (current_action "idle")
	            	 (Available_space ?truck_space1&:(>= ?truck_space1 ?package_size)))
		  (shortest_path (city1 ?truck_city)
					(city2 ?start_city)
					(time ?s_path1&:(eq ?s_path1 ?s_path)))))	
	(not (and (truck (truck_no ?truck_num)					;there must be no truck in the different place which reaches the package early
	            	 (current_city ?truck_city1)				
		    	 (current_action "idle")
	            	 (Available_space ?truck_space2&:(>= ?truck_space2 ?package_size)))
		  (shortest_path (city1 ?truck_city1)
				 (city2 ?start_city)
				 (time ?s_path2&:(< ?s_path2 ?s_path)))))						   
	(not (and (and (queue $? ?package $?)
				(package (package_no ?package)
							(size_of_package ?pa_size)))
				(truck (Available_space ?avail_space&:(> ?avail_space ?pa_size))
						(current_action "idle"))))
	(not (and (package (package_no ?number)					;no package to which a truck can reach early than the one which it is going to pick now
					   (size_of_package ?new_p_size&:(< ?new_p_size ?truck_space))
					   (status "arrived")
					   (depart_city ?dep_city)
						(arrival_time ?time))
			   (shortest_path (city1 ?truck_city)
							  (city2 ?dep_city)
							  (time ?new_time&:(< ?new_time ?s_path)))))					
	
	
=>
	(modify ?truck 	(destination_city $?d ?start_city)
			(current_action "going to pick a package")
			(waiting_time =(+ ?w_time (- ?time ?r_time)))
			(busy_time =(+ ?s_path ?b_time))
			(non_del_time =(+ ?ndeltime ?s_path))
			(reached_time =(+ ?time ?s_path))
			(numofpack $?nop ?pnum))
	(modify ?pack (status "waiting to pick up")
			(wait_time ?s_path)))






(defrule package-to-queue					;defrule to handle the situation when there is no truck left to pick the arrived package.
											; Hence the package will be moved to queue where it will be waiting for an idle truck to pick up.
	(declare (salience -2))												
	(current-time ?time) 

	?pack <- (package (package_no ?num)
			  (arrival_time ?time)
			  (depart_city ?dcity)
			  (status "arrived")
			  (size_of_package ?psize))
	
	(not (truck (truck_no ?tno)
		(current_action "idle")
		(Available_space ?space&:(>= ?space ?psize))))
	?queue <- (queue $?packages) 

=>
	(modify ?pack (status "waiting in queue"))
 	(retract ?queue) 
 	(assert (queue ?num $?packages)))




(defrule truck-with-package					;defrule to handle the situation where the truck picks up the package from its 
											;depart city and heading towards its destination city via "via-city" if exists.
	?pack <- (package (package_no ?pnum)
		 	(depart_city ?start_city)
			(deliver_city ?end_city)
			(size_of_package ?package_size)
		 	(status "waiting to pick up")) 
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack $? ?pnum $?)
	       	         (destination_city ?start_city $?d)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "going to pick a package")
			 (Available_space ?space_available)
			 (space_occupied ?occupied)
			 (tot_space_occupied ?tot_occupied)
			 (packages_carrying ?packs))	
	(shortest_path (city1 ?start_city) 
			(city2 ?end_city)
			(time ?between_path)
			(via ?via_city $?))
	(shortest_path (city1 ?start_city) 
			(city2 ?via_city)
			(time ?between_via_path))

	
=>
	(modify ?truck 	(destination_city $?d ?end_city)
			(current_city ?via_city)
			(current_action "in route to deliver a package")
			(busy_time =(+ ?s_path ?between_via_path))
			(reached_time =(+ ?r_time ?between_via_path))
			(del_time =(+ ?deltime ?between_via_path))
			(Available_space =(- ?space_available ?package_size))
			(space_occupied =(+ ?occupied ?package_size))
			(tot_space_occupied =(+ ?tot_occupied ?package_size))
			(packages_carrying =(+ ?packs 1)))
	(modify ?pack (status "in-transit")
		      (ppick_up_time ?r_time)))


(defrule truck-with-package-directly				;defrule to handle the situation where the truck picks up the package from its 
													;depart city and heading towards destination city directly. There is no via-city
	?pack <- (package (package_no ?pnum)
		 	(depart_city ?start_city)
			(deliver_city ?end_city)
			(size_of_package ?package_size)
		 	(status "waiting to pick up")) 
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack $? ?pnum $?)
	       	         (destination_city ?start_city $?d)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "going to pick a package")
			 (Available_space ?space_available)
			 (space_occupied ?occupied)
			 (tot_space_occupied ?tot_occupied)
			 (packages_carrying ?packs))
	
	(not (package (package_no ?p_num&:(> ?p_num ?pnum))
			(arrival_time ?a_time&:(<= ?a_time ?r_time))
			(status "arrived")))
	
	(shortest_path (city1 ?start_city) 
			(city2 ?end_city)
			(time ?between_path))
			

	
=>
	(modify ?truck 	(destination_city $?d ?end_city)
			(current_city ?start_city)
			(current_action "in route to deliver a package")
			(busy_time =(+ ?s_path ?between_path))
			(reached_time =(+ ?r_time ?between_path))
			(del_time =(+ ?deltime ?between_path))
			(Available_space =(- ?space_available ?package_size))
			(space_occupied =(+ ?occupied ?package_size))
			(tot_space_occupied =(+ ?tot_occupied ?package_size))
			(packages_carrying =(+ ?packs 1)))
	(modify ?pack (status "in-transit")
		      (ppick_up_time ?r_time)))




(defrule truck-loading-other-packages-ontheway			;defrule to describe the scenario where truck picking up the package just arrived on its way and
	(declare (salience -2))								;is after the its current destination to deliver already loaded package
	(current-time ?time)	
	(package (package_no ?pno)
	        (depart_city ?start_city)
		(deliver_city ?d_city)
		(size_of_package ?psize)
		(status "in-transit"|"waiting to pick up"))
	?pack <- (package (package_no ?pnum)			
		 	(depart_city ?via_city)
			(deliver_city ?end_city)
			(size_of_package ?package_size)
		 	(status "arrived")
			(arrival_time ?time)
			(exp_delivery_time ?package_delivery_time))
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack $?nop ?pno)
	       	  (current_city ?via_city)
			 (destination_city ?d_city $?dest_city)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "in route to deliver a package")
			 (Available_space ?space_available&:(>= ?space_available ?package_size))
			 (space_occupied ?occupied)
			 (tot_space_occupied ?tot_occupied)
			 (packages_carrying ?packs))
	(shortest_path (city1 ?via_city) 
		       (city2 ?end_city)
			(time ?between_path)
			(via $?))
	(shortest_path (city1 ?via_city) 
		       (city2 ?d_city)
			(time ?between_path1&:(< ?between_path1 ?between_path))
			(via $?))
	(shortest_path (city1 ?start_city) 
		       (city2 ?d_city)
			(time ?between_path2)
			(via ?via_city $?))
=>
	(modify ?truck 	(destination_city $?dest_city ?d_city ?end_city)
			(numofpack $?nop ?pno ?pnum)
			(current_city ?via_city)
			(current_action "in route to deliver a package")
			(busy_time =(+ ?s_path ?between_path1))
			(reached_time =(+ ?r_time ?between_path1))
			(del_time =(+ ?deltime ?between_path1))
			(Available_space =(- ?space_available ?package_size))
			(space_occupied =(+ ?package_size ?occupied))
			(tot_space_occupied =(+ ?tot_occupied ?package_size))
			(packages_carrying =(+ ?packs 1)))
	(modify ?pack (status "in-transit")
		      (ppick_up_time ?r_time)))



(defrule truck-loading-other-packages-ontheway2			;defrule to describe the scenario where truck picking up the package just arrived which 
	(declare (salience -2))								;is on the way of its destination to deliver already loaded package. First delivers picked package
	(current-time ?time)	
	(package (package_no ?pno)
	        (depart_city ?start_city)
		(deliver_city ?d_city)
		(size_of_package ?psize)
		(status "in-transit"|"waiting to pick up"))
	?pack <- (package (package_no ?pnum)
			
		 	(depart_city ?via_city)
			(deliver_city ?end_city)
			(size_of_package ?package_size)
		 	(status "arrived")
			(arrival_time ?time)
			(exp_delivery_time ?package_delivery_time))
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack $?nop ?pno)
	       	  	 (current_city ?via_city)
			 (destination_city ?d_city $?dest_city)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "in route to deliver a package")
			 (Available_space ?space_available&:(>= ?space_available ?package_size))
			 (space_occupied ?occupied)
			 (tot_space_occupied ?tot_occupied)
			 (packages_carrying ?packs))
	(shortest_path (city1 ?via_city) 
		       (city2 ?end_city)
			(time ?between_path)
			(via $?))
	(shortest_path (city1 ?via_city) 
		       (city2 ?d_city)
			(time ?between_path1&:(> ?between_path1 ?between_path))
			(via $?))
	(shortest_path (city1 ?start_city) 
		       (city2 ?d_city)
			(time ?between_path2)
			(via ?via_city $?))
=>
	(modify ?truck 	(destination_city ?end_city ?d_city $?dest_city)
			(numofpack ?pnum ?pno $?nop)
			(current_city ?start_city)
			(current_action "in route to deliver a package")
			(busy_time =(+ ?s_path ?between_path))
			(reached_time =(+ ?r_time ?between_path))
			(del_time =(+ ?deltime ?between_path))
			(Available_space =(- ?space_available ?package_size))
			(space_occupied =(+ ?package_size ?occupied))
			(tot_space_occupied =(+ ?tot_occupied ?package_size))
			(packages_carrying =(+ ?packs 1)))
	(modify ?pack (status "in-transit")
		      (ppick_up_time ?r_time)))




(defrule truck-deliver-package-still-left					;defrule to handle the situation where the truck carrying multiple packages delivers them 
															;by updating appropriate times and status of both truck and package
	(current-time ?curr)
	?pack <- (package (package_no ?pnum)
		 	(depart_city ?scity)
			(deliver_city ?ecity)
			(arrival_time ?atime)
		 	(status "in-transit")
			(wait_time ?pwtime)
			(size_of_package ?p_size)
			(exp_delivery_time ?package_delivery_time))
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack ?pnum $?nop)
			 (current_city ?start_city)
	       	 (destination_city ?ecity ?d $?del)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "in route to deliver a package")
			 (Available_space ?a_space))
	(not (package (package_no ?p_num&:(> ?p_num ?pnum))
			(arrival_time ?a_time&:(<= ?a_time ?r_time))
			(status "waiting to pick up"|"arrived")))
	(shortest_path (city1 ?start_city)
			(city2 ?ecity)
            		(time ?btime))
	(shortest_path (city1 ?ecity)
			(city2 ?d)
            		(time ?b1time))
	
	?counter <- (packages-delivered-counter ?pack_delivered)
	?avg <- (AveragePackageReport   (tot_wait_time ?avgwtime)
					(packs_delivered_ontime ?ontime)
					(packs_delivered_late ?late)
					(late_time ?latetime))
=>
	(retract ?counter)
	(modify ?truck 	(current_city ?ecity)
			(numofpack $?nop)
			(destination_city ?d $?del)
			(current_action "in route to deliver a package")
			(busy_time =(+ ?s_path ?b1time))
			(reached_time =(+ ?r_time ?b1time))
			(del_time =(+ ?deltime ?b1time))
			(Available_space =(+ ?a_space ?p_size))
			(space_occupied =(- ?a_space ?p_size)))
	(assert (packages-delivered-counter =(+ ?pack_delivered 1)))
	(modify ?pack (status "delivered")
		      (pdelivery_time ?r_time))
	(modify ?avg (tot_wait_time =(+ ?avgwtime ?pwtime))))



(defrule truck-deliver-packages									;defrule to handle the situation where the truck carrying single package delivers it 
																;by updating appropriate times and status of both truck and package
	
	(current-time ?curr)
	?pack <- (package (package_no ?pnum)
			
		 	(depart_city ?start_city)
			(deliver_city ?ecity)
			(arrival_time ?atime)
		 	(status "in-transit")
			(wait_time ?pwtime)
			(size_of_package ?p_size)
			(exp_delivery_time ?package_delivery_time))
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack ?pnum)
			 (current_city ?scity)
	       	 	 (destination_city ?ecity)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time&:(<= ?r_time ?curr))
			 (del_time ?deltime)
			 (current_action "in route to deliver a package")
			 (Available_space ?a_space))
	(shortest_path (city1 ?scity)
			(city2 ?ecity)
            		(time ?btime))
	?counter <- (packages-delivered-counter ?pack_delivered)
	?avg <- (AveragePackageReport   (tot_wait_time ?avgwtime)
					(packs_delivered_ontime ?ontime)
					(packs_delivered_late ?late)
					(late_time ?latetime))
	
=>
	(retract ?counter)
	(modify ?truck 	(current_city ?ecity)
			(numofpack)
			(destination_city ?ecity)
			(current_action "delivered package")
			(busy_time (+ ?btime ?s_path))
			(reached_time ?r_time)
			(del_time (+ ?btime ?deltime))
			(Available_space =(+ ?a_space ?p_size))
			(space_occupied 0))
	(assert (packages-delivered-counter =(+ ?pack_delivered 1)))
	(modify ?pack (status "delivered")
		      (pdelivery_time ?r_time))
	(modify ?avg (tot_wait_time =(+ ?avgwtime ?pwtime))))
	
	
(defrule truck-deliver-leftout-packages									;defrule to handle the situation where the truck to deliver the package 
																		;when no more packages left to deliver by other trucks. i.e time doesn't update now
	
	(current-time ?curr)
	?pack <- (package (package_no ?pnum)
			
		 	(depart_city ?start_city)
			(deliver_city ?ecity)
			(arrival_time ?atime)
		 	(status "in-transit")
			(wait_time ?pwtime)
			(size_of_package ?p_size)
			(exp_delivery_time ?package_delivery_time))
	(not (package (status "arrived"|"waiting to pick up")))
	?truck <- (truck (truck_no ?truck_no)
			 (numofpack ?pnum)
			 (current_city ?scity)
	       	 	 (destination_city ?ecity)
			 (busy_time ?s_path)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (del_time ?deltime)
			 (current_action "in route to deliver a package")
			 (Available_space ?a_space))
	(shortest_path (city1 ?scity)
			(city2 ?ecity)
            		(time ?btime))
	?counter <- (packages-delivered-counter ?pack_delivered)
	?avg <- (AveragePackageReport   (tot_wait_time ?avgwtime)
					(packs_delivered_ontime ?ontime)
					(packs_delivered_late ?late)
					(late_time ?latetime))
	
=>
	(assert (waitingtime (- (+ ?btime ?r_time) ?curr)))
	(retract ?counter)
	(modify ?truck 	(current_city ?ecity)
			(numofpack)
			(destination_city ?ecity)
			(current_action "delivered package")
			(busy_time =(+ ?s_path ?btime))
			(reached_time =(+ ?r_time ?btime))
			(del_time =(+ ?deltime ?btime))
			(Available_space =(+ ?a_space ?p_size))
			(space_occupied 0))
	(assert (packages-delivered-counter =(+ ?pack_delivered 1)))
	(assert (all))
	(modify ?pack (status "delivered")
		      (pdelivery_time ?r_time))
	(modify ?avg (tot_wait_time =(+ ?avgwtime ?pwtime))))




(defrule truck-ready-to-pickup						;defrule to handle the situation where truck after delivering all the 	
	?truck <- (truck (truck_no ?truck_no)			;package carrying and ready to pick up the next suitable package
			 (current_city ?curr)
			 (busy_time ?b_time)
			 (waiting_time ?w_time)
			 (reached_time ?r_time)
			 (current_action "delivered package")
			 (packages_carrying ?no_of_packs)
			 (non_del_time ?ndeltime)
			 (Available_space ?space)
			 (del_time ?deltime))
	(not (package 	(arrival_time ?a_time&:(< ?a_time ?r_time))
			(status "arrived")))
	(not (truck (reached_time ?r_time1&:(< ?r_time1 ?r_time))
		    (current_action "going to pick a package"|"in route to deliver a package"|"delivered package")))
=>
	(modify ?truck  (destination_city)
			(numofpack)
			(busy_time ?b_time)
			(waiting_time ?w_time)
			(current_city ?curr)
			(current_action "idle")
			(reached_time ?r_time)
			(Available_space ?space)
			(non_del_time ?ndeltime)
			(del_time ?deltime)))




(defrule queue-to-truck						;defrule to handle the situation where a right package from queue will be moved into
	(current-time ?time) 					;the idle truck.
	(package (package_no ?pnum)
		 (status "arrived")
		 (arrival_time ?time)) 
	?pack <- (package (package_no ?package)
		 (status "waiting in queue")
		 (arrival_time ?time1&:(< ?time1 ?time))
	 	 (size_of_package ?package_size1)
		 (depart_city ?start_city1)
		 (deliver_city ?end_city1)
		 (exp_delivery_time ?package_delivery_time1)
		 (wait_time ?p_w_time))
	(not (package (package_no ?package1)
		 (status "waiting in queue")
		 (arrival_time ?time2&:(< ?time2 ?time1))
		 (exp_delivery_time ?package_delivery_time2&:(< ?package_delivery_time2 ?package_delivery_time1))))
	?queue <- (queue $?d ?package $?p)
	?truck <- (truck (truck_no ?truck_no)
	       		 (current_city ?curr_city)
			 (current_action "idle")
	       		 (Available_space ?truck_space&:(>= ?truck_space ?package_size1))
			 (reached_time ?rea_time)
			 (busy_time ?ttime)
			 (waiting_time ?t_w_time)
			 (non_del_time ?ndeltime))
	(shortest_path (city1 ?curr_city)
			(city2 ?start_city1)
			(time ?s_path))
	(not (and (truck (truck_no ?truck_num)
	            	  (current_city ?truck_city)
		    	  (current_action "idle")
	            	  (Available_space ?truck_space&:(>= ?truck_space ?package_size1))
		    	  (reached_time ?r_time))
		  (shortest_path (city1 ?truck_city)
				 (city2 ?start_city1)
				 (time ?s_path1&:(< ?s_path1 ?s_path)))))
				
	
=>
	(retract ?queue)
	(assert (queue $?d $?p))
	(modify ?truck 	(destination_city ?start_city1)
			(numofpack ?package)
			(current_action "going to pick a package")
			(reached_time (+ ?time ?s_path))
			(busy_time =(+ ?s_path ?ttime))
			(waiting_time =(+ ?t_w_time (- ?time ?rea_time)))
			(non_del_time =(+ ?ndeltime ?s_path)))
	(modify ?pack (status "waiting to pick up")
			(ppick_up_time =(+ ?rea_time ?s_path))
			(wait_time =(- (+ ?rea_time ?s_path) ?time1))))



(defrule queue-to-truck2					;defrule to handle the situation where a right package from queue will be moved into
	(current-time ?time) 					;the idle truck which became idle at the same time
	?pack <- (package (package_no ?package)
		 	 (status "waiting in queue")
			 (arrival_time ?atime&:(<= ?atime ?time))
		 	 (size_of_package ?package_size1)
			 (depart_city ?start_city1)
			 (deliver_city ?end_city1)
		 	 (exp_delivery_time ?package_delivery_time1)
		 	 (wait_time ?p_w_time))
	(not (package (package_no ?package1)
		 (status "waiting in queue")
		 (exp_delivery_time ?package_delivery_time2&:(< ?package_delivery_time2 ?package_delivery_time1))))
	?queue <- (queue $?d ?package $?p)
			
	?truck <- (truck (truck_no ?truck_no)
	       		 (current_city ?curr_city)
			 (current_action "idle")
	       		 (Available_space ?truck_space&:(>= ?truck_space ?package_size1))
			 (reached_time ?rea_time&:(<= ?rea_time ?time))
			 (busy_time ?ttime)
			 (waiting_time ?t_w_time)
			 (non_del_time ?ndeltime))
	(shortest_path (city1 ?curr_city)
			(city2 ?start_city1)
			(time ?s_path))
	(not (and (truck (truck_no ?truck_num)
	            	  (current_city ?truck_city)
		    	  (current_action "idle")
	            	  (Available_space ?truck_space&:(>= ?truck_space ?package_size1))
		    	  (reached_time ?r_time))
		  (shortest_path (city1 ?truck_city)
				 (city2 ?start_city1)
				 (time ?s_path1&:(< ?s_path1 ?s_path)))))
				
	
=>
	(retract ?queue)
	(assert (queue $?d $?p))
	(modify ?truck 	(destination_city ?start_city1)
			(numofpack ?package)
			(current_action "going to pick a package")
			(busy_time =(+ ?s_path ?ttime))
			(reached_time (+ ?time ?s_path))
			(waiting_time =(+ ?t_w_time (- ?time ?rea_time)))
			(non_del_time =(+ ?ndeltime ?s_path)))
	(modify ?pack (status "waiting to pick up")
			(ppick_up_time =(+ ?rea_time ?s_path))
			(wait_time =(- (+ ?rea_time ?s_path) ?atime))))

			
;Rule to generate the Truck Report Header. After all the packages are delivered, and all trucks become idle


(defrule Truck-Report-Header
	
	(not (truck (truck_no ?tnum)
		(current_action "delivered package"|"in route to deliver a package"|"going to pick a package")))
	(not (package (package_no ?pack)
			(status "arrived"|"waiting to pick up"|"in-transit")))
	(all)
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))

=>
	(printout t crlf)
	(printout t crlf)
	(printout t crlf)
	(printout t crlf)
(printout t "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------" crlf)
(printout t "                                                                           TRUCK REPORT                                                                                                       " crlf)
(printout t "==============================================================================================================================================================================================" crlf)
(printout t " Truck#  |	WAIT-TIME | TOTAL BUSY-TIME |  %BUSY-TIME  | #TOTAL-PACKAGES-CARRIED | AVG.%OCCUPANCY | NON_DELIVERTY TRAVEL TIME | %NON_DELIVERY TIME	| DELIVERTY TRAVEL TIME | %DELIVERY TIME	| " crlf)						
(printout t "===============================================================================================================================================================================================" crlf)
	(assert (truck-header done))
	(assert (trucks 0)))




;defrule which dives the Truck Report. Each and every detail of the Truck can be known by this report	


(defrule TruckReport																		
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(current-time ?time)
	(truck-header done)
	?t <- (trucks ?trucks_done)
	?truck <- (truck (truck_no ?t_no)
		(current_city ?truck_city)
		(current_action "idle")
		(waiting_time ?w_time&:(neq ?w_time 0))
		(busy_time ?b_time&:(neq ?b_time 0))
		(packages_carrying ?packs)
		(non_del_time ?ndeltime)
		(space_occupied ?occupied_space)	
		(Available_space ?avail_space)
		(tot_space_occupied ?tot_occupied)
		(del_time ?deltime))
	(not (truck (truck_no ?tnum&:(< ?tnum ?t_no))
		(current_action ?action&:(eq ?action "idle"))))
		(waitingtime ?tw)
=>
	(retract ?truck)
	(printout t "    ")
	(format t "%-08d" ?t_no)
	(format t "%-015d" (+ ?tw ?w_time))
	(format t "%-015d" ?b_time)
	(format t "%-020f" (/ (* ?b_time 100) ?time))
	(format t "%-022d" ?packs)
	(format t "%-025f" (* (/ ?tot_occupied (* ?avail_space ?packs)) 100))
	(format t "%-020d" ?ndeltime)
	(format t "%-023f" (* (/ ?ndeltime (+ ?w_time ?b_time)) 100))
	(format t "%-022d" ?deltime)
	(format t "%-015f" (* (/ ?deltime (+ ?w_time ?b_time)) 100))
	(printout t crlf)
	(assert (trucks (+ 1 ?trucks_done))))


;defrule which dives the Truck Report which are not used to deliver single package. 
;Each and every detail of the Truck can be known by this report
(defrule TruckReport-notused					
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(current-time ?time)
	(truck-header done)
	?t <- (trucks ?trucks_done)
	?truck <- (truck (truck_no ?t_no)
		(current_city ?truck_city)
		(destination_city nil)
		(current_action ?status&:(eq ?status "idle"))
		(waiting_time ?w_time)
		(busy_time 0)
		(packages_carrying 0)
		(space_occupied 0)
		(tot_space_occupied ?tot_occupied)
		(non_del_time 0)
		(del_time 0))
	(not (truck (truck_no ?tnum&:(< ?tnum ?t_no))))
=>
	(retract ?truck ?t)
	(printout t "    ")
	(format t "%-08d" ?t_no)
	(format t "%-015d" ?w_time)
	(format t "%-018d" 0)
	(format t "%-20f" 0)
	(format t "%-022d" 0)
	(format t "%-20f" 0)
	(format t "%-028d" 0)
	(format t "%-20f" 0)
	(printout t crlf)
	(assert (trucks =(+ 1 ?trucks_done))))

	
;defrule for generating package Report header	

(defrule Package-Report-Header
	(truck-header done)
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(trucks ?truck_counter&:(eq ?truck_counter ?*tcounter*))
	?avg <- (AveragePackageReport   (tot_wait_time ?avgwtime&:(neq ?avgwtime 0))
				(packs_delivered_ontime ?ontime)
				(packs_delivered_late ?late)
				(late_time ?latetime))
=>

(modify ?avg (tot_wait_time 0))
(printout t crlf)
(printout t crlf)
(printout t crlf)
(printout t crlf)
(printout t " ---------------------------------------------------------------------------------------------------------------------- " crlf)
(printout t "                                                   PACKAGE REPORT                                                       " crlf)
(printout t " ====================================================================================================================== " crlf)
(printout t "  PACKAGE#  |  TOTAL WAIT-TIME  | 	 PICK-UP-TIME	 |   DELIVERY-TIME  	| ON-TIME DELIVERY STATUS  | DELIVERY DELAYED BY |" crlf)
(printout t " ====================================================================================================================== " crlf)
(assert (package-header done))
(assert (packages 0)))

;defrule which dives the Package Report. Each and every detail of the Package can be known by this report
	

(defrule PackageReport					
		
	(truck-header done)
	(package-header done)
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(trucks ?truck_counter&:(eq ?truck_counter ?*tcounter*))
	?p1 <- (packages ?packages_done)
	?p <- (package (package_no ?package)
		 (depart_city ?start_city)
		 (deliver_city ?end_city)
		 (wait_time ?w_time)
		 (ppick_up_time ?ptime)
		 (arrival_time ?atime)
		 (pdelivery_time ?dtime)
		 (exp_delivery_time ?exptime)
		 (status "delivered"))
	(shortest_path (city1 Orlando)
			(city2 ?start_city)
			(time ?time1))
	(shortest_path (city1 ?start_city)
			(city2 ?end_city)
			(time ?time2))
	(not (package (package_no ?pack&:(< ?pack ?package))
			(status ?stat&:(eq ?stat "delivered"))))
	?avg <- (AveragePackageReport   (tot_wait_time ?avgwtime)
				(packs_delivered_ontime ?ontime)
				(packs_delivered_late ?late)
				(late_time ?latetime))

=>
	(retract ?p1)
	(modify ?p (status "done"))
	(printout t "    ")
	(format t "%-018d" ?package)
	(format t "%-022d" (- ?ptime ?atime))
	(format t "%-019d" ?ptime)
	(format t "%-018d" ?dtime)
	(bind ?res (<= (+ ?time1 ?time2) (- ?exptime ?atime)))
	(format t "%-022s" ?res)
	(bind ?delay 0)
	(if (neq ?res TRUE) 
	 then (bind ?delay (- (+ ?time1 ?time2) (- ?exptime ?atime))))
	(if (<= ?delay 0)
		then (format t "%-023d" 0)
		else (and (format t "%-023d" ?delay)
					(modify ?avg  
					(tot_wait_time =(+ ?avgwtime (- ?ptime ?atime)))
			(late_time =(+ ?latetime ?delay))
			(packs_delivered_late =(+ ?late 1))
			(packs_delivered_ontime =(- ?ontime 1)))))
	(printout t crlf)
	(assert (packages (+ ?packages_done 1))))


(defrule Package-Average-Report-Header
	(truck-header done)
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(trucks ?truck_counter&:(eq ?truck_counter ?*tcounter*))
	(package-header done)
	(packages ?pdone_counter&:(eq ?pdone_counter ?*pcounter*))
=>
(printout t crlf)
(printout t crlf)
(printout t crlf)
(printout t crlf)
(printout t " ------------------------------------------------------------------------------------------------------------------------------" crlf)
(printout t "                                                 PACKAGE AVERAGE REPORT                                                       " crlf)
(printout t " ==============================================================================================================================" crlf)
(printout t "   AVG WAIT TIME  | PCKG DELIVERED ON TIME | PCKG DELIVERED LATE | AVERAGE LATENESS OF LATE PCKG | AVERAGE LATENESS OF ALL PCKG|" crlf)
(printout t " ==============================================================================================================================" crlf)
(assert (average-header done))	)


;defrule which dives the Average Report of Package . Average time details of the package can be known by this report

(defrule Package-Average-Report							
	
	(truck-header done)
	(packages-delivered-counter ?counter&:(eq ?counter ?*pcounter*))
	(trucks ?truck_counter&:(eq ?truck_counter ?*tcounter*))
	(package-header done)
	(packages ?pdone_counter&:(eq ?pdone_counter ?*pcounter*))
	(average-header done)
	(AveragePackageReport (tot_wait_time ?tot_wtime)
				(packs_delivered_ontime ?pdel)
				(packs_delivered_late ?plate)
				(late_time ?latetime))

=>
	(printout t "       ")
	(format t "%-025f" (/ ?tot_wtime 50))
	(format t "%-023d" ?pdel)
	(format t "%-025d" ?plate)
	(if (eq ?plate 0) then  (format t "%-025d" 0)
			  else (format t "%-024f" (/ ?latetime ?plate)))
	(format t "%-025f" (/ ?latetime 50))
	(printout t crlf)
	(halt))
	



