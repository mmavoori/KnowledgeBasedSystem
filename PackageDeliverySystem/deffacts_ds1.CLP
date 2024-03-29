;Templates
(deftemplate city 
	(slot city_name)
	(multislot connected_cities))

(deftemplate shortest_path
	(slot city1)
	(slot city2)
	(slot time)
	(multislot via))

;Template for Trucks, each slots handles the required times to be noted and location of the truck with status

(deftemplate truck
	(slot truck_no)
	(slot current_city)
	(multislot destination_city)
	(slot current_action)
	(slot waiting_time)
	(slot busy_time)
	(slot reached_time)
	(slot Available_space)
	(slot space_occupied)
	(slot packages_carrying)
	(slot tot_space_occupied)
	(slot non_del_time)
	(slot del_time)
	(multislot numofpack))

;Template for Package, each slots handles the required times to be noted and location of the package with status

(deftemplate package
	(slot package_no)
	(slot depart_city)
	(slot deliver_city)
	(slot size_of_package)
	(slot arrival_time)
	(slot exp_delivery_time)
	(slot ppick_up_time)
	(slot pdelivery_time)
	(slot wait_time)
	(slot status))

(deftemplate AveragePackageReport
	(slot tot_wait_time)
	(slot packs_delivered_ontime)
	(slot packs_delivered_late)
	(slot late_time))


;deffacts



(deffacts Packages-Are-US 
	(city (city_name Tallahassee)
	      (connected_cities LakeCity 2))
	(city (city_name LakeCity)
	      (connected_cities Gainesville 1 Jacksonville 1 Tallahassee 2))
	(city (city_name Jacksonville)
	      (connected_cities St.Augustine 1 LakeCity 1))
	(city (city_name Gainesville)
	      (connected_cities St.Augustine 1 Ocala 1 LakeCity 1))
	(city (city_name St.Augustine)
	      (connected_cities Jacksonville 1 Gainesville 1 Orlando 2 WestPalm 3))
	(city (city_name Ocala)
	      (connected_cities Tampa 2 Gainesville 1 Orlando 1))
	(city (city_name Orlando)
	      (connected_cities Tampa 1 St.Augustine 2 Ocala 1 WestPalm 3))
	(city (city_name Tampa)
	      (connected_cities Orlando 1 Ocala 2 Ft.Myers 2))
	(city (city_name Ft.Myers)
	      (connected_cities Tampa 2 WestPalm 3))
	(city (city_name WestPalm)
	      (connected_cities Orlando 3 Ft.Myers 3 St.Augustine 3 Miami 2))
	(city (city_name Miami)
	      (connected_cities WestPalm 2 KeyWest 3))	
	(city (city_name KeyWest)
	      (connected_cities Miami 3))
	(truck (truck_no 1)
	       (current_city Orlando)
	       (current_action "idle")
	       (Available_space 15)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
                (tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(truck (truck_no 2)
	       (current_city LakeCity)
	       (current_action "idle")
	       (Available_space 5)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
		(tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(truck (truck_no 3)
	       (current_city Jacksonville)
	       (current_action "idle")
	       (Available_space 5)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
		(tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(truck (truck_no 4)
	       (current_city Ft.Myers)
	       (current_action "idle")
	       (Available_space 10)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
		(tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(truck (truck_no 5)
	       (current_city Miami)
	       (current_action "idle")
	       (Available_space 15)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
		(tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(truck (truck_no 6)
	       (current_city Orlando)
	       (current_action "idle")
	       (Available_space 10)
	       (waiting_time 0)
	       (busy_time 0)
		(space_occupied 0)
		(tot_space_occupied 0)
		(reached_time 0)
		(packages_carrying 0)
		(non_del_time 0)
		(del_time 0))
	(package (package_no 1)
		 (status "arrived")
		 (depart_city Orlando)
		 (deliver_city Jacksonville)
		 (size_of_package 4)
		 (arrival_time 1)
	 	 (exp_delivery_time 15)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 2)
		 (status "arrived")
		 (depart_city Gainesville)
		 (deliver_city Jacksonville)
		 (size_of_package 1)
		 (arrival_time 1)
	 	 (exp_delivery_time 15)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 3)
		 (status "arrived")
		 (depart_city WestPalm)
		 (deliver_city St.Augustine)
		 (size_of_package 3)
		 (arrival_time 4)
	 	 (exp_delivery_time 10)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 4)
		 (status "arrived")
		 (depart_city KeyWest)
		 (deliver_city St.Augustine)
		 (size_of_package 4)
		 (arrival_time 4)
	 	 (exp_delivery_time 10)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 5)
		 (status "arrived")
		 (depart_city Gainesville)
		 (deliver_city Tallahassee)
		 (size_of_package 9)
		 (arrival_time 5)
	 	 (exp_delivery_time 10)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 6)
		 (status "arrived")
		 (depart_city Jacksonville)
		 (deliver_city Orlando)
		 (size_of_package 10)
		 (arrival_time 8)
	 	 (exp_delivery_time 18)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 7)
		 (status "arrived")
		 (depart_city Jacksonville)
		 (deliver_city Miami)
		 (size_of_package 5)
		 (arrival_time 8)
	 	 (exp_delivery_time 25)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 8)
		 (status "arrived")
		 (depart_city Ft.Myers)
		 (deliver_city KeyWest)
		 (size_of_package 4)
		 (arrival_time 9)
	 	 (exp_delivery_time 20)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 9)
		 (status "arrived")
		 (depart_city Orlando)
		 (deliver_city KeyWest)
		 (size_of_package 4)
		 (arrival_time 9)
	 	 (exp_delivery_time 22)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 10)
		 (status "arrived")
		 (depart_city WestPalm)
		 (deliver_city Miami)
		 (size_of_package 2)
		 (arrival_time 9)
	 	 (exp_delivery_time 16)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 11)
		 (status "arrived")
		 (depart_city Miami)
		 (deliver_city Ocala)
		 (size_of_package 4)
		 (arrival_time 10)
	 	 (exp_delivery_time 20)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 12)
		 (status "arrived")
		 (depart_city Gainesville)
		 (deliver_city Orlando)
		 (size_of_package 7)
		 (arrival_time 11)
	 	 (exp_delivery_time 17)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 13)
		 (status "arrived")
		 (depart_city Tampa)
		 (deliver_city Tallahassee)
		 (size_of_package 12)
		 (arrival_time 12)
	 	 (exp_delivery_time 25)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 14)
		 (status "arrived")
		 (depart_city Miami)
		 (deliver_city Orlando)
		 (size_of_package 5)
		 (arrival_time 20)
	 	 (exp_delivery_time 30)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 15)
		 (status "arrived")
		 (depart_city Ocala)
		 (deliver_city Orlando)
		 (size_of_package 7)
		 (arrival_time 30)
	 	 (exp_delivery_time 40)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 16)
		 (status "arrived")
		 (depart_city Orlando)
		 (deliver_city LakeCity)
		 (size_of_package 6)
		 (arrival_time 40)
	 	 (exp_delivery_time 45)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 17)
		 (status "arrived")
		 (depart_city Jacksonville)
		 (deliver_city Tallahassee)
		 (size_of_package 5)
		 (arrival_time 65)
	 	 (exp_delivery_time 80)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 18)
		 (status "arrived")
		 (depart_city Tallahassee)
		 (deliver_city Gainesville)
		 (size_of_package 8)
		 (arrival_time 80)
	 	 (exp_delivery_time 100)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 19)
		 (status "arrived")
		 (depart_city St.Augustine)
		 (deliver_city Tallahassee)
		 (size_of_package 5)
		 (arrival_time 90)
	 	 (exp_delivery_time 110)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 20)
		 (status "arrived")
		 (depart_city WestPalm)
		 (deliver_city Ft.Myers)
		 (size_of_package 4)
		 (arrival_time 110)
	 	 (exp_delivery_time 120)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 21)
		 (status "arrived")
		 (depart_city St.Augustine)
		 (deliver_city Ft.Myers)
		 (size_of_package 7)
		 (arrival_time 110)
	 	 (exp_delivery_time 120)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 22)
		 (status "arrived")
		 (depart_city Jacksonville)
		 (deliver_city KeyWest)
		 (size_of_package 2)
		 (arrival_time 120)
	 	 (exp_delivery_time 150)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 23)
		 (status "arrived")
		 (depart_city Miami)
		 (deliver_city KeyWest)
		 (size_of_package 4)
		 (arrival_time 150)
	 	 (exp_delivery_time 155)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 24)
		 (status "arrived")
		 (depart_city Miami)
		 (deliver_city Gainesville)
		 (size_of_package 5)
		 (arrival_time 150)
	 	 (exp_delivery_time 165)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 25)
		 (status "arrived")
		 (depart_city Miami)
		 (deliver_city Tallahassee)
		 (size_of_package 5)
		 (arrival_time 150)
	 	 (exp_delivery_time 170)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 26)
		 (status "arrived")
		 (depart_city Tallahassee)
		 (deliver_city LakeCity)
		 (size_of_package 8)
		 (arrival_time 180)
	 	 (exp_delivery_time 200)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 27)
		 (status "arrived")
		 (depart_city LakeCity)
		 (deliver_city Tallahassee)
		 (size_of_package 7)
		 (arrival_time 190)
	 	 (exp_delivery_time 200)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 28)
		 (status "arrived")
		 (depart_city Tallahassee)
		 (deliver_city KeyWest)
		 (size_of_package 12)
		 (arrival_time 200)
	 	 (exp_delivery_time 250)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 29)
		 (status "arrived")
		 (depart_city St.Augustine)
		 (deliver_city KeyWest)
		 (size_of_package 3)
		 (arrival_time 200)
	 	 (exp_delivery_time 260)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(package (package_no 30)
		 (status "arrived")
		 (depart_city Tampa)
		 (deliver_city Jacksonville)
		 (size_of_package 9)
		 (arrival_time 210)
	 	 (exp_delivery_time 240)
		 (wait_time 0)
		 (pdelivery_time 0)
		 (ppick_up_time 0))
	(queue) 
	(current-time 0)
	(packages-delivered-counter 0)
	(AveragePackageReport (tot_wait_time 0)
				(packs_delivered_ontime 30)
				(packs_delivered_late 0)
				(late_time 0)))
(defglobal ?*pcounter* = 30)
(defglobal ?*tcounter* = 6)