import heapq
from collections import defaultdict, deque
from datetime import datetime, timedelta
import uuid

class Flight:
    """Flight class to represent individual flights"""
    def __init__(self, flight_id, origin, destination, departure_time, arrival_time, 
                 capacity, price, distance):
        self.flight_id = flight_id
        self.origin = origin
        self.destination = destination
        self.departure_time = departure_time
        self.arrival_time = arrival_time
        self.capacity = capacity
        self.price = price
        self.distance = distance
        self.booked_seats = 0
        self.passengers = []  # List of passenger IDs
        self.waiting_list = deque()  # Queue for waiting passengers
    
    def is_available(self):
        return self.booked_seats < self.capacity
    
    def get_available_seats(self):
        return self.capacity - self.booked_seats
    
    def __str__(self):
        return f"Flight {self.flight_id}: {self.origin} -> {self.destination} " \
               f"({self.departure_time} - {self.arrival_time}) - ${self.price}"

class Passenger:
    """Passenger class to store passenger information"""
    def __init__(self, passenger_id, name, email, phone):
        self.passenger_id = passenger_id
        self.name = name
        self.email = email
        self.phone = phone
        self.bookings = []  # List of booking IDs
    
    def __str__(self):
        return f"Passenger {self.passenger_id}: {self.name} ({self.email})"

class Booking:
    """Booking class to represent flight bookings"""
    def __init__(self, booking_id, passenger_id, flight_id, booking_time, status="CONFIRMED"):
        self.booking_id = booking_id
        self.passenger_id = passenger_id
        self.flight_id = flight_id
        self.booking_time = booking_time
        self.status = status  # CONFIRMED, CANCELLED, WAITLISTED
    
    def __str__(self):
        return f"Booking {self.booking_id}: Passenger {self.passenger_id} " \
               f"-> Flight {self.flight_id} ({self.status})"

class FlightNode:
    """Node for linked list implementation of flight schedule"""
    def __init__(self, flight):
        self.flight = flight
        self.next = None

class FlightSchedule:
    """Linked list implementation for dynamic flight scheduling"""
    def __init__(self):
        self.head = None
        self.size = 0
    
    def add_flight(self, flight):
        """Add flight to schedule in chronological order"""
        new_node = FlightNode(flight)
        
        if not self.head or flight.departure_time < self.head.flight.departure_time:
            new_node.next = self.head
            self.head = new_node
        else:
            current = self.head
            while (current.next and 
                   current.next.flight.departure_time < flight.departure_time):
                current = current.next
            new_node.next = current.next
            current.next = new_node
        
        self.size += 1
    
    def remove_flight(self, flight_id):
        """Remove flight from schedule"""
        if not self.head:
            return False
        
        if self.head.flight.flight_id == flight_id:
            self.head = self.head.next
            self.size -= 1
            return True
        
        current = self.head
        while current.next:
            if current.next.flight.flight_id == flight_id:
                current.next = current.next.next
                self.size -= 1
                return True
            current = current.next
        
        return False
    
    def get_flights_from_airport(self, airport):
        """Get all flights departing from a specific airport"""
        flights = []
        current = self.head
        while current:
            if current.flight.origin == airport:
                flights.append(current.flight)
            current = current.next
        return flights
    
    def display_schedule(self):
        """Display all flights in schedule"""
        flights = []
        current = self.head
        while current:
            flights.append(current.flight)
            current = current.next
        return flights

class AirportGraph:
    """Graph implementation for airports and routes"""
    def __init__(self):
        self.airports = set()
        self.flights = defaultdict(list)  # adjacency list of flights
        self.distances = defaultdict(lambda: defaultdict(lambda: float('inf')))
        self.prices = defaultdict(lambda: defaultdict(lambda: float('inf')))
    
    def add_airport(self, airport):
        """Add airport to the graph"""
        self.airports.add(airport)
    
    def add_flight_route(self, flight):
        """Add flight route to the graph"""
        origin, destination = flight.origin, flight.destination
        self.airports.add(origin)
        self.airports.add(destination)
        
        self.flights[origin].append(flight)
        self.distances[origin][destination] = min(
            self.distances[origin][destination], flight.distance
        )
        self.prices[origin][destination] = min(
            self.prices[origin][destination], flight.price
        )
    
    def dijkstra_shortest_path(self, start, end, criteria='distance'):
        """
        Dijkstra's algorithm to find shortest path
        criteria: 'distance' or 'price'
        """
        if start not in self.airports or end not in self.airports:
            return None, float('inf')
        
        # Priority queue: (cost, current_airport, path)
        pq = [(0, start, [start])]
        visited = set()
        
        while pq:
            current_cost, current_airport, path = heapq.heappop(pq)
            
            if current_airport in visited:
                continue
            
            visited.add(current_airport)
            
            if current_airport == end:
                return path, current_cost
            
            # Check all flights from current airport
            for flight in self.flights[current_airport]:
                next_airport = flight.destination
                
                if next_airport not in visited:
                    if criteria == 'distance':
                        edge_cost = flight.distance
                    else:  # price
                        edge_cost = flight.price
                    
                    new_cost = current_cost + edge_cost
                    new_path = path + [next_airport]
                    heapq.heappush(pq, (new_cost, next_airport, new_path))
        
        return None, float('inf')
    
    def find_all_routes(self, start, end, max_stops=2):
        """Find all possible routes with limited stops"""
        routes = []
        
        def dfs(current, destination, path, stops, total_distance, total_price):
            if stops > max_stops:
                return
            
            if current == destination and len(path) > 1:
                routes.append({
                    'path': path.copy(),
                    'stops': stops,
                    'total_distance': total_distance,
                    'total_price': total_price
                })
                return
            
            for flight in self.flights[current]:
                next_airport = flight.destination
                if next_airport not in path:  # Avoid cycles
                    path.append(next_airport)
                    dfs(next_airport, destination, path, stops + 1,
                        total_distance + flight.distance,
                        total_price + flight.price)
                    path.pop()
        
        dfs(start, end, [start], 0, 0, 0)
        return routes

class AirlineManagementSystem:
    """Main airline management system class"""
    def __init__(self):
        self.airport_graph = AirportGraph()
        self.flight_schedule = FlightSchedule()
        self.passengers = {}  # HashMap of passenger_id -> Passenger
        self.bookings = {}    # HashMap of booking_id -> Booking
        self.flights = {}     # HashMap of flight_id -> Flight
    
    def add_airport(self, airport_code):
        """Add new airport to the system"""
        self.airport_graph.add_airport(airport_code)
        print(f"Airport {airport_code} added successfully.")
    
    def add_flight(self, flight_id, origin, destination, departure_time, 
                   arrival_time, capacity, price, distance):
        """Add new flight to the system"""
        flight = Flight(flight_id, origin, destination, departure_time,
                       arrival_time, capacity, price, distance)
        
        self.flights[flight_id] = flight
        self.flight_schedule.add_flight(flight)
        self.airport_graph.add_flight_route(flight)
        
        print(f"Flight {flight_id} added successfully.")
    
    def register_passenger(self, name, email, phone):
        """Register new passenger"""
        passenger_id = str(uuid.uuid4())[:8]
        passenger = Passenger(passenger_id, name, email, phone)
        self.passengers[passenger_id] = passenger
        
        print(f"Passenger registered successfully. ID: {passenger_id}")
        return passenger_id
    
    def book_flight(self, passenger_id, flight_id):
        """Book a flight for a passenger"""
        if passenger_id not in self.passengers:
            print("Passenger not found.")
            return None
        
        if flight_id not in self.flights:
            print("Flight not found.")
            return None
        
        flight = self.flights[flight_id]
        passenger = self.passengers[passenger_id]
        
        booking_id = str(uuid.uuid4())[:8]
        booking_time = datetime.now()
        
        if flight.is_available():
            # Confirm booking
            booking = Booking(booking_id, passenger_id, flight_id, booking_time, "CONFIRMED")
            self.bookings[booking_id] = booking
            
            flight.booked_seats += 1
            flight.passengers.append(passenger_id)
            passenger.bookings.append(booking_id)
            
            print(f"Booking confirmed! Booking ID: {booking_id}")
            return booking_id
        else:
            # Add to waiting list
            booking = Booking(booking_id, passenger_id, flight_id, booking_time, "WAITLISTED")
            self.bookings[booking_id] = booking
            
            flight.waiting_list.append(passenger_id)
            passenger.bookings.append(booking_id)
            
            print(f"Flight full. Added to waiting list. Booking ID: {booking_id}")
            return booking_id
    
    def cancel_booking(self, booking_id):
        """Cancel a booking"""
        if booking_id not in self.bookings:
            print("Booking not found.")
            return False
        
        booking = self.bookings[booking_id]
        flight = self.flights[booking.flight_id]
        passenger = self.passengers[booking.passenger_id]
        
        if booking.status == "CONFIRMED":
            # Remove from confirmed passengers
            flight.booked_seats -= 1
            flight.passengers.remove(booking.passenger_id)
            
            # Check waiting list for next passenger
            if flight.waiting_list:
                next_passenger_id = flight.waiting_list.popleft()
                
                # Find the waitlisted booking and confirm it
                for bid, b in self.bookings.items():
                    if (b.passenger_id == next_passenger_id and 
                        b.flight_id == booking.flight_id and 
                        b.status == "WAITLISTED"):
                        b.status = "CONFIRMED"
                        flight.booked_seats += 1
                        flight.passengers.append(next_passenger_id)
                        print(f"Passenger {next_passenger_id} moved from waiting list to confirmed.")
                        break
        
        elif booking.status == "WAITLISTED":
            # Remove from waiting list
            try:
                flight.waiting_list.remove(booking.passenger_id)
            except ValueError:
                pass  # Already removed
        
        booking.status = "CANCELLED"
        passenger.bookings.remove(booking_id)
        
        print(f"Booking {booking_id} cancelled successfully.")
        return True
    
    def find_shortest_route(self, origin, destination, criteria='distance'):
        """Find shortest route between airports"""
        path, cost = self.airport_graph.dijkstra_shortest_path(origin, destination, criteria)
        
        if path:
            print(f"\nShortest route by {criteria}:")
            print(f"Path: {' -> '.join(path)}")
            print(f"Total {criteria}: {cost}")
            return path, cost
        else:
            print(f"No route found from {origin} to {destination}")
            return None, float('inf')
    
    def find_all_routes(self, origin, destination, max_stops=2):
        """Find all possible routes"""
        routes = self.airport_graph.find_all_routes(origin, destination, max_stops)
        
        if routes:
            print(f"\nAll routes from {origin} to {destination}:")
            for i, route in enumerate(routes, 1):
                print(f"{i}. {' -> '.join(route['path'])} "
                      f"(Stops: {route['stops']}, Distance: {route['total_distance']}, "
                      f"Price: ${route['total_price']})")
        else:
            print(f"No routes found from {origin} to {destination}")
        
        return routes
    
    def search_flights(self, origin, destination=None, date=None):
        """Search for flights"""
        available_flights = []
        
        if destination:
            # Direct flights
            for flight in self.airport_graph.flights[origin]:
                if flight.destination == destination:
                    available_flights.append(flight)
        else:
            # All flights from origin
            available_flights = self.airport_graph.flights[origin]
        
        if available_flights:
            print(f"\nAvailable flights from {origin}:")
            for flight in available_flights:
                seats_available = flight.get_available_seats()
                waiting_count = len(flight.waiting_list)
                print(f"{flight} | Available: {seats_available} | Waiting: {waiting_count}")
        else:
            print(f"No flights found from {origin}")
        
        return available_flights
    
    def get_passenger_bookings(self, passenger_id):
        """Get all bookings for a passenger"""
        if passenger_id not in self.passengers:
            print("Passenger not found.")
            return []
        
        passenger = self.passengers[passenger_id]
        bookings = [self.bookings[bid] for bid in passenger.bookings if bid in self.bookings]
        
        print(f"\nBookings for {passenger.name}:")
        for booking in bookings:
            flight = self.flights[booking.flight_id]
            print(f"{booking} | Flight: {flight}")
        
        return bookings
    
    def display_flight_schedule(self):
        """Display current flight schedule"""
        flights = self.flight_schedule.display_schedule()
        print("\nCurrent Flight Schedule:")
        print("-" * 80)
        for flight in flights:
            print(f"{flight} | Booked: {flight.booked_seats}/{flight.capacity}")
    
    def get_system_stats(self):
        """Get system statistics"""
        total_flights = len(self.flights)
        total_passengers = len(self.passengers)
        total_bookings = len([b for b in self.bookings.values() if b.status == "CONFIRMED"])
        total_waitlisted = len([b for b in self.bookings.values() if b.status == "WAITLISTED"])
        
        print(f"\nSystem Statistics:")
        print(f"Total Airports: {len(self.airport_graph.airports)}")
        print(f"Total Flights: {total_flights}")
        print(f"Total Passengers: {total_passengers}")
        print(f"Confirmed Bookings: {total_bookings}")
        print(f"Waitlisted Bookings: {total_waitlisted}")

def main():
    """Main function to demonstrate the airline management system"""
    system = AirlineManagementSystem()
    
    # Add airports
    airports = ['NYC', 'LAX', 'CHI', 'MIA', 'SEA', 'DEN']
    for airport in airports:
        system.add_airport(airport)
    
    # Add flights
    flights_data = [
        ('FL001', 'NYC', 'LAX', '08:00', '11:00', 150, 500, 2445),
        ('FL002', 'LAX', 'NYC', '14:00', '22:00', 150, 550, 2445),
        ('FL003', 'NYC', 'CHI', '09:00', '11:30', 120, 300, 790),
        ('FL004', 'CHI', 'LAX', '13:00', '15:30', 120, 400, 1745),
        ('FL005', 'NYC', 'MIA', '10:00', '13:00', 100, 350, 1090),
        ('FL006', 'MIA', 'LAX', '15:00', '18:00', 100, 450, 2342),
        ('FL007', 'SEA', 'NYC', '07:00', '15:00', 130, 600, 2408),
        ('FL008', 'DEN', 'MIA', '11:00', '15:30', 110, 400, 1726),
        ('FL009', 'CHI', 'SEA', '16:00', '18:30', 90, 350, 1721),
        ('FL010', 'LAX', 'SEA', '12:00', '14:30', 140, 250, 954)
    ]
    
    for flight_data in flights_data:
        system.add_flight(*flight_data)
    
    # Register passengers
    passengers = [
        ('John Doe', 'john@email.com', '123-456-7890'),
        ('Jane Smith', 'jane@email.com', '234-567-8901'),
        ('Bob Johnson', 'bob@email.com', '345-678-9012'),
        ('Alice Brown', 'alice@email.com', '456-789-0123')
    ]
    
    passenger_ids = []
    for passenger_data in passengers:
        pid = system.register_passenger(*passenger_data)
        passenger_ids.append(pid)
    
    print("\n" + "="*50)
    print("AIRLINE MANAGEMENT SYSTEM DEMO")
    print("="*50)
    
    # Demo functionality
    print("\n1. FLIGHT SEARCH DEMO")
    system.search_flights('NYC', 'LAX')
    
    print("\n2. ROUTE PLANNING DEMO")
    system.find_shortest_route('NYC', 'SEA', 'distance')
    system.find_shortest_route('NYC', 'SEA', 'price')
    system.find_all_routes('NYC', 'LAX', max_stops=1)
    
    print("\n3. BOOKING DEMO")
    # Book flights for passengers
    booking1 = system.book_flight(passenger_ids[0], 'FL001')  # John -> NYC to LAX
    booking2 = system.book_flight(passenger_ids[1], 'FL003')  # Jane -> NYC to CHI
    booking3 = system.book_flight(passenger_ids[2], 'FL001')  # Bob -> NYC to LAX
    
    print("\n4. PASSENGER BOOKINGS")
    system.get_passenger_bookings(passenger_ids[0])
    
    print("\n5. CANCELLATION DEMO")
    if booking1:
        system.cancel_booking(booking1)
    
    print("\n6. FLIGHT SCHEDULE")
    system.display_flight_schedule()
    
    print("\n7. SYSTEM STATISTICS")
    system.get_system_stats()

if __name__ == '__main__':
    main()