--!optimize 2
--!native
--!strict
--draft 4

type i53 = number
type i24 = number

type Ty = { i53 }
type ArchetypeId = number

type Column = { any }

type ArchetypeEdge = {
	add: Archetype,
	remove: Archetype,
}

type Archetype = {
	id: number,
	edges: { [i53]: ArchetypeEdge },
	types: Ty,
	type: string | number,
	entities: { number },
	columns: { Column },
	records: { [number]: number },
}

type Record = {
	archetype: Archetype,
	row: number,
	dense: i24,
	componentRecord: ArchetypeMap,
}

type EntityIndex = { dense: { [i24]: i53 }, sparse: { [i53]: Record } }

type ArchetypeRecord = number
--[[
TODO:
{
	index: number,
	count: number,
	column: number
}

]]

type ArchetypeMap = {
	cache: { ArchetypeRecord },
	first: ArchetypeMap,
	second: ArchetypeMap,
	parent: ArchetypeMap,
	size: number,
}

type ComponentIndex = { [i24]: ArchetypeMap }

type Archetypes = { [ArchetypeId]: Archetype }

type ArchetypeDiff = {
	added: Ty,
	removed: Ty,
}

local HI_COMPONENT_ID 		= 256

local EcsOnAdd 				= HI_COMPONENT_ID + 1
local EcsOnRemove 			= HI_COMPONENT_ID + 2
local EcsOnSet 				= HI_COMPONENT_ID + 3
local EcsWildcard 			= HI_COMPONENT_ID + 4
local EcsChildOf 			= HI_COMPONENT_ID + 5
local EcsComponent  		= HI_COMPONENT_ID + 6
local EcsRest 				= HI_COMPONENT_ID + 7

local ECS_PAIR_FLAG 		= 0x8
local ECS_ID_FLAGS_MASK 	= 0x10
local ECS_ENTITY_MASK 		= bit32.lshift(1, 24)
local ECS_GENERATION_MASK 	= bit32.lshift(1, 16)

local function addFlags(isPair: boolean): number
	local typeFlags = 0x0

	if isPair then
		typeFlags = bit32.bor(typeFlags, ECS_PAIR_FLAG) -- HIGHEST bit in the ID.
	end
	if false then
		typeFlags = bit32.bor(typeFlags, 0x4) -- Set the second flag to true
	end
	if false then
		typeFlags = bit32.bor(typeFlags, 0x2) -- Set the third flag to true
	end
	if false then
		typeFlags = bit32.bor(typeFlags, 0x1) -- LAST BIT in the ID.
	end

	return typeFlags
end

local function ECS_COMBINE(source: number, target: number): i53
	return (source * 268435456) + (target * ECS_ID_FLAGS_MASK)
end

local function ECS_IS_PAIR(e: number): boolean
	return if e > ECS_ENTITY_MASK then (e % ECS_ID_FLAGS_MASK) // ECS_PAIR_FLAG ~= 0 else false
end

-- HIGH 24 bits LOW 24 bits
local function ECS_GENERATION(e: i53): i24
	return if e > ECS_ENTITY_MASK then (e // ECS_ID_FLAGS_MASK) % ECS_GENERATION_MASK else 0
end

local function ECS_GENERATION_INC(e: i53)
	if e > ECS_ENTITY_MASK then
		local flags = e // ECS_ID_FLAGS_MASK
		local id = flags // ECS_ENTITY_MASK
		local generation = flags % ECS_GENERATION_MASK

		return ECS_COMBINE(id, generation + 1) + flags
	end
	return ECS_COMBINE(e, 1)
end

-- FIRST gets the high ID
local function ECS_ENTITY_T_HI(e: i53): i24
	return if e > ECS_ENTITY_MASK then (e // ECS_ID_FLAGS_MASK) % ECS_ENTITY_MASK else e
end

-- SECOND
local function ECS_ENTITY_T_LO(e: i53): i24
	return if e > ECS_ENTITY_MASK then (e // ECS_ID_FLAGS_MASK) // ECS_ENTITY_MASK else e
end

local function STRIP_GENERATION(e: i53): i24
	return ECS_ENTITY_T_LO(e)
end

local function ECS_PAIR(pred: i53, obj: i53): i53
	return ECS_COMBINE(ECS_ENTITY_T_LO(obj), ECS_ENTITY_T_LO(pred)) + addFlags(--[[isPair]] true) :: i53
end

local ERROR_ENTITY_NOT_ALIVE = "Entity is not alive"
local ERROR_GENERATION_INVALID = "INVALID GENERATION"

local function getAlive(index: EntityIndex, e: i24): i53
	local denseArray = index.dense
    local id = denseArray[ECS_ENTITY_T_LO(e)]

	if id then
		local currentGeneration = ECS_GENERATION(id)
		local gen = ECS_GENERATION(e)
		if gen == currentGeneration then
			return id
		end

		error(ERROR_GENERATION_INVALID)
	end

	error(ERROR_ENTITY_NOT_ALIVE)
end

local function sparseGet(entityIndex, id)
	return entityIndex.sparse[getAlive(entityIndex, id)]
end

-- ECS_PAIR_FIRST, gets the relationship target / obj / HIGH bits
local function ECS_PAIR_RELATION(entityIndex, e)
	return getAlive(entityIndex, ECS_ENTITY_T_HI(e))
end

-- ECS_PAIR_SECOND gets the relationship / pred / LOW bits
local function ECS_PAIR_OBJECT(entityIndex, e)
	return getAlive(entityIndex, ECS_ENTITY_T_LO(e))
end

local function next_entity_id(entity_index: EntityIndex, index: i24): i53
	--local id = ecs_combine(index, 0)
	local id = index
	entity_index.sparse[id] = {
		dense = index,
	} :: Record
	entity_index.dense[index] = id

	return id
end

local function transition_archetype(entity_index: EntityIndex, to: Archetype,
	dst_row: i24, from: Archetype, src_row: i24)

	local columns = from.columns
	local src_entities = from.entities
	local dst_entities = to.entities
	local dst_columns = to.columns
	local tr = to.records
	local types = from.types

	for i, column in columns do
		-- Retrieves the new column index from the source archetype's record from each component
		-- We have to do this because the columns are tightly packed and indexes may not correspond to each other.
		local target_column = dst_columns[tr[types[i]]]

		-- Sometimes target column may not exist, e.g. when you remove a component.
		if target_column then
			target_column[dst_row] = column[src_row]
		end
		-- If the entity is the last row in the archetype then swapping it would be meaningless.
		local last = #column
		if src_row ~= last then
			-- Swap rempves columns to ensure there are no holes in the archetype.
			column[src_row] = column[last]
		end
		column[last] = nil
	end

	local sparse = entity_index.sparse
	local moved_away = #src_entities

	-- Move the entity from the source to the destination archetype.
	-- Because we have swapped columns we now have to update the records
	-- corresponding to the entities' rows that were swapped.
	local e1 = src_entities[src_row]
	local e2 = src_entities[moved_away]

	if src_row ~= moved_away then
		src_entities[src_row] = e2
	end

	src_entities[moved_away] = nil :: any
	dst_entities[dst_row] = e1

	local record1 = sparse[e1]
	local record2 = sparse[e2]

	record1.row = dst_row
	record2.row = src_row
end

local function archetype_append(entity: number, archetype: Archetype): number
	local entities = archetype.entities
	local length = #entities + 1
	entities[length] = entity
	return length
end

local function new_entity(entity_id: i53, record: Record, archetype: Archetype): Record
	local row = archetype_append(entity_id, archetype)
	record.archetype = archetype
	record.row = row
	return record
end

local function move_entity(entity_index: EntityIndex, entity_id: i53, record: Record, to: Archetype)
	local src_row = record.row
	local from = record.archetype
	local dst_row = archetype_append(entity_id, to)
	transition_archetype(entity_index, to, dst_row, from, src_row)
	record.archetype = to
	record.row = dst_row
end

local function hash(arr: { number }): string
	return table.concat(arr, "_")
end

local function ensure_id_record(
	id_index: ComponentIndex,
	id: number
): ArchetypeMap
	local idr = id_index[id]

	if not idr then
		idr = ({ size = 0, cache = {} } :: any) :: ArchetypeMap
		id_index[id] = idr
	end

	return idr
end

local function ECS_ID_IS_WILDCARD(e: i53): boolean
	assert(ECS_IS_PAIR(e))
	local first = ECS_ENTITY_T_HI(e)
	local second = ECS_ENTITY_T_LO(e)
	return first == EcsWildcard or second == EcsWildcard
end

local function archetype_of(world: any, types: { i24 }, prev: Archetype?): Archetype
	local ty = hash(types)

	local archetype_id = world.next_archetype_id + 1
	world.next_archetype_id = archetype_id

	local length = #types
	local columns = (table.create(length) :: any) :: { Column }
	local id_index = world.id_index

	local records = {}
	for i, id in types do
		local idr = ensure_id_record(id_index, id)
		idr.cache[archetype_id] = i
		idr.size += 1
		records[id] = i
		if ECS_IS_PAIR(id) then
			local relation = ECS_PAIR_RELATION(world.entity_index, id)
			local obj = ECS_PAIR_OBJECT(world.entity_index, id)

			local r = ECS_PAIR(relation, EcsWildcard)
			local o = ECS_PAIR(EcsWildcard, obj)

			local idr_r = ensure_id_record(id_index, r)
			local idr_o = ensure_id_record(id_index, o)

			records[r] = i
			records[o] = i

			idr_r.cache[archetype_id] = i
			idr_o.cache[archetype_id] = i

			idr_r.size += 1
			idr_o.size += 1
		end
		columns[i] = {}
	end

	local archetype: Archetype = {
		columns = columns,
		edges = {},
		entities = {},
		id = archetype_id,
		records = records,
		type = ty,
		types = types,
	}

	world.archetype_index[ty] = archetype
	world.archetypes[archetype_id] = archetype

	return archetype
end

export type World = {
	archetype_index: { [string]: Archetype },
	archetypes: Archetypes,
	id_index: ComponentIndex,
	entity_index: EntityIndex,
	next_archetype_id: number,
	next_id: number,
	next_entity_id: number,
	root_archetype: Archetype
}

local function entity(world: World): i53
	local entity_id = world.next_entity_id + 1
	world.next_entity_id = entity_id
	return next_entity_id(world.entity_index, entity_id + EcsRest)
end

-- TODO:
-- should have an additional `nth` parameter which selects the nth target
-- this is important when an entity can have multiple relationships with the same target
local function target(world: World, entity: i53, relation: i24--[[, nth: number]]): i24?
	local entity_index = world.entity_index
	local record = entity_index.sparse[entity]
	local archetype = record.archetype
	if not archetype then
		return nil
	end

	local idr = world.id_index[ECS_PAIR(relation, EcsWildcard)]
	if not idr then
		return nil
	end

	local archetype_record = idr.cache[archetype.id]
	if not archetype_record then
		return nil
	end

	return ECS_PAIR_OBJECT(entity_index, archetype.types[archetype_record])
end

local function parent(world: World, entity: i53)
	return target(world, entity, EcsChildOf)
end

local function ensure_archetype(world: World, types, prev): Archetype
	if #types < 1 then
		return world.root_archetype
	end

	local ty = hash(types)
	local archetype = world.archetype_index[ty]
	if archetype then
		return archetype
	end

	return archetype_of(world, types, prev)
end

local function find_insert(types: { i53 }, to_add: i53): number
	for i, id in types do
		if id == to_add then
			return -1
		end
		if id > to_add then
			return i
		end
	end
	return #types + 1
end

local function find_archetype_with(world: World, node: Archetype, component_id: i53): Archetype
	local types = node.types
	-- Component IDs are added incrementally, so inserting and sorting
	-- them each time would be expensive. Instead this insertion sort can find the insertion
	-- point in the types array.

	local destination_type = table.clone(node.types) :: { i53 }
	local at = find_insert(types, component_id)
	if at == -1 then
		-- If it finds a duplicate, it just means it is the same archetype so it can return it
		-- directly instead of needing to hash types for a lookup to the archetype.
		return node
	end
	table.insert(destination_type, at, component_id)

	return ensure_archetype(world, destination_type, node)
end

local function ensure_edge(archetype: Archetype, component_id: i53): ArchetypeEdge
	local edges = archetype.edges
	local edge = edges[component_id]
	if not edge then
		edge = {} :: any
		edges[component_id] = edge
	end
	return edge
end

local function archetype_traverse_add(world: World, component_id: i53, from: Archetype): Archetype
	from = from or world.root_archetype

	local edge = ensure_edge(from, component_id)
	local add = edge.add
	if not add then
		-- Save an edge using the component ID to the archetype to allow
		-- faster traversals to adjacent archetypes.
		add = find_archetype_with(world, from, component_id)
		edge.add = add :: never
	end

	return add
end

local function add(world: World, entity_id: i53, component_id: i53)
	local entity_index = world.entity_index
	local record = entity_index.sparse[entity_id]
	local from = record.archetype
	local to = archetype_traverse_add(world, component_id, from)
	if from and not (from == world.root_archetype) then
		move_entity(entity_index, entity_id, record, to)
	else
		if #to.types > 0 then
			new_entity(entity_id, record, to)
		end
	end
end

-- Symmetric like `World.add` but idempotent
local function set(world: World, entity_id: i53, id: i53, data: unknown)
	local record = world.entity_index.sparse[entity_id]
	local from = record.archetype
	local to = archetype_traverse_add(world, id, from)

	if from == to then
		-- If the archetypes are the same it can avoid moving the entity
		-- and just set the data directly.
		local archetype_record = to.records[id]
		from.columns[archetype_record][record.row] = data
		-- Should fire an OnSet event here.
		return
	end

	if from then
		-- If there was a previous archetype, then the entity needs to move the archetype
		move_entity(world.entity_index, entity_id, record, to)
	else
		if #to.types > 0 then
			-- When there is no previous archetype it should create the archetype
			new_entity(entity_id, record, to)
		end
	end

	local archetype_record = to.records[id]
	to.columns[archetype_record][record.row] = data
end

local function new_component(world: World): i53
	local component_id = world.next_id + 1
	if component_id > HI_COMPONENT_ID then
		-- IDs are partitioned into ranges because component IDs are not nominal,
		-- so it needs to error when IDs intersect into the entity range.
		error("Too many components, consider using world:entity() instead to create components.")
	end
	world.next_id = component_id
	local id = next_entity_id(world.entity_index, component_id)
	add(world, id, EcsComponent)
	return id
end


local function archetype_traverse_remove(world: World, component_id: i53, from: Archetype): Archetype
	local edge = ensure_edge(from, component_id)

	local remove = edge.remove
	if not remove then
		local to = table.clone(from.types) :: { i53 }
		local at = table.find(to, component_id)
		if not at then
			return from
		end
		table.remove(to, at)
		remove = ensure_archetype(world, to, from)
		edge.remove = remove :: never
	end

	return remove
end

local function remove(world: World, entity_id: i53, id: i53)
	local entity_index = world.entity_index
	local record = entity_index.sparse[entity_id]
	local src_archetype = record.archetype
	local dst_archetype = archetype_traverse_remove(world, id, src_archetype)

	if src_archetype and not (src_archetype == dst_archetype) then
		move_entity(entity_index, entity_id, record, dst_archetype)
	end
end

-- should reuse this logic in World.set instead of swap removing in transition_archetype
local function destruct_columns(columns: { Column }, count: number, row: number)
	if row == count then
		for _, column in columns do
			column[count] = nil
		end
	else
		for _, column in columns do
			column[row] = column[count]
			column[count] = nil
		end
	end
end

local function archetype_delete(world: World, id: i53)
	local id_index = world.id_index
	local archetypes_map = id_index[id]
	local archetypes = world.archetypes

	if archetypes_map then
		for archetype_id in archetypes_map.cache do
			for _, entity in archetypes[archetype_id].entities do
				remove(world, entity, id)
			end
		end

		id_index[id] = nil :: any
	end
end

local function delete(world: World, entity_id: i53)
	local record = world.entity_index.sparse[entity_id]
	if not record then
		return
	end
	local entity_index = world.entity_index
	local sparse, dense = entity_index.sparse, entity_index.dense
	local archetype = record.archetype
	local row = record.row

	archetype_delete(world, entity_id)
	-- TODO: should traverse linked )component records to pairs including entity_id
	archetype_delete(world, ECS_PAIR(entity_id, EcsWildcard))
	archetype_delete(world, ECS_PAIR(EcsWildcard, entity_id))

	if archetype then
		local entities = archetype.entities
		local last = #entities

		if row ~= last then
			local entity_to_move = entities[last]
			dense[record.dense] = entity_to_move
			sparse[entity_to_move] = record
		end

		entities[row], entities[last] = entities[last], nil :: any

		local columns = archetype.columns

		destruct_columns(columns, last, row)
	end

	sparse[entity_id] = nil :: any
	dense[#dense] = nil :: any

end

local function clear(world: World, entity_id: i53)
	--TODO: use sparse_get (stashed)
	local record = world.entity_index.sparse[entity_id]
	if not record then
		return
	end

	local root_archetype = world.root_archetype
	local archetype = record.archetype

	if archetype == nil or archetype == root_archetype then
		return
	end

	move_entity(world.entity_index, entity_id, record, root_archetype)
end

-- Keeping the function as small as possible to enable inlining
local function fetch(record: Record, component_id: i24): any
	local archetype = record.archetype
	if not archetype then
		return nil
	end

	local archetype_record = archetype.records[component_id]

	if not archetype_record then
		return nil
	end

	return archetype.columns[archetype_record][record.row]
end

local function get(world: World, entity_id: i53, a: i53, b: i53?, c: i53?, d: i53?, e: i53?): ...any
	local id = entity_id
	local record = world.entity_index.sparse[id]
	if not record then
		return nil
	end

	local va = fetch(record, a)

	if b == nil then
		return va
	elseif c == nil then
		return va, fetch(record, b)
	elseif d == nil then
		return va, fetch(record, b), fetch(record, c)
	elseif e == nil then
		return va, fetch(record, b), fetch(record, c), fetch(record, d)
	else
		error("args exceeded")
	end
end

-- the less creation the better
local function actual_no_operation() end
local function noop(_self: Query, ...): () -> ()
	return actual_no_operation :: any
end

local EmptyQuery = {
	__iter = noop,
	next = noop,
	replace = noop,
	without = function(self)
		return self
	end
}

export type Query = typeof(EmptyQuery)

type CompatibleArchetype = { archetype: Archetype, indices: { number } }

local function replace_mult(row, columns, ...)
	for i, column in columns do
		column[row] = select(i, ...)
	end
end

local function prepared_query(compatible_archetypes: { Archetype },
	components: { i53? }, indices: { { number } })

	local query_length = #components

	local last_archetype = 1
	local archetype: Archetype = compatible_archetypes[last_archetype]

	if not archetype then
		return EmptyQuery
	end

	local query_output = {}

	local entities = archetype.entities
	local i = #entities

	local function query_next(): ...any
		local entity_id = entities[i]
		while entity_id == nil do
			last_archetype += 1
			archetype = compatible_archetypes[last_archetype]

			if not archetype then
				return
			end

			entities = archetype.entities
			i = #entities
			entity_id = entities[i]
		end

		local row = i
		i-=1

		local columns = archetype.columns
		local tr = indices[last_archetype]

		if query_length == 1 then
			return entity_id, columns[tr[1]][row]
		elseif query_length == 2 then
			return entity_id, columns[tr[1]][row], columns[tr[2]][row]
		elseif query_length == 3 then
			return entity_id, columns[tr[1]][row], columns[tr[2]][row], columns[tr[3]][row]
		elseif query_length == 4 then
			return entity_id, columns[tr[1]][row], columns[tr[2]][row], columns[tr[3]][row], columns[tr[4]][row]
		elseif query_length == 5 then
			return entity_id,
				columns[tr[1]][row],
				columns[tr[2]][row],
				columns[tr[3]][row],
				columns[tr[4]][row],
				columns[tr[5]][row]
		elseif query_length == 6 then
			return entity_id,
				columns[tr[1]][row],
				columns[tr[2]][row],
				columns[tr[3]][row],
				columns[tr[4]][row],
				columns[tr[5]][row],
				columns[tr[6]][row]
		elseif query_length == 7 then
			return entity_id,
				columns[tr[1]][row],
				columns[tr[2]][row],
				columns[tr[3]][row],
				columns[tr[4]][row],
				columns[tr[5]][row],
				columns[tr[6]][row],
				columns[tr[7]][row]
		elseif query_length == 8 then
			return entity_id,
				columns[tr[1]][row],
				columns[tr[2]][row],
				columns[tr[3]][row],
				columns[tr[4]][row],
				columns[tr[5]][row],
				columns[tr[6]][row],
				columns[tr[7]][row],
				columns[tr[8]][row]
		end

		for i in components do
			query_output[i] = columns[tr[i]][row]
		end

		return entity_id, unpack(query_output, 1, query_length)
	end

	local function without(self, ...): Query
		local without_components = { ... }
		for i = #compatible_archetypes, 1, -1 do
			local archetype = compatible_archetypes[i]
			local records = archetype.records
			local should_remove = false

			for _, component_id in without_components do
				if records[component_id] then
					should_remove = true
					break
				end
			end

			if should_remove then
				table.remove(compatible_archetypes, i)
			end
		end

		return self
	end

	local function iter()
        last_archetype = 1
		archetype = compatible_archetypes[1]
		entities = archetype.entities
		i = #entities

		return query_next
	end

	local function replace(_, fn: any)
        for i, archetype in compatible_archetypes do
			local tr = indices[i]
			local columns = archetype.columns

			for row in archetype.entities do
				if query_length == 1 then
					local a = columns[tr[1]]
					local pa = fn(a[row])

					a[row] = pa
				elseif query_length == 2 then
					local a = columns[tr[1]]
					local b = columns[tr[2]]

					a[row], b[row] = fn(a[row], b[row])
				elseif query_length == 3 then
					local a = columns[tr[1]]
					local b = columns[tr[2]]
					local c = columns[tr[3]]

					a[row], b[row], c[row] = fn(a[row], b[row], c[row])
				elseif query_length == 4 then
					local a = columns[tr[1]]
					local b = columns[tr[2]]
					local c = columns[tr[3]]
					local d = columns[tr[4]]

					a[row], b[row], c[row], d[row] = fn(
						a[row], b[row], c[row], d[row])
				else
					for i = 1, query_length do
						query_output[i] = columns[tr[i]][row]
					end
					replace_mult(row, columns, fn(unpack(query_output)))
				end
			end
		end
	end

	local it = {
		__iter = iter,
		next = query_next,
		without = without,
		replace = replace
	}

	return setmetatable(it, it) :: any
end

local function query(world: World, ...: number): Query
	-- breaking?
	if (...) == nil then
		error("Missing components")
	end

	local indices: { { number } } = {}
	local compatible_archetypes: { Archetype } = {}
	local length = 0

	local components: { number } = { ... }
	local archetypes: { Archetype } = world.archetypes :: any

	local first_archetype_map: ArchetypeMap
	local id_index = world.id_index

	for _, id in components do
		local map: ArchetypeMap = id_index[id] :: any
		if not map then
			return EmptyQuery
		end

		if (first_archetype_map :: any) == nil or first_archetype_map.size < map.size then
			first_archetype_map = map
		end
	end

	for id in first_archetype_map.cache do
		local archetype = archetypes[id]
		local archetype_records = archetype.records

		local records: { number } = {}
		local skip = false

		for i, component_id in components do
			local index = archetype_records[component_id]
			if not index then
				skip = true
				break
			end
			-- index should be index.offset
			records[i] = index
		end

		if skip then
			continue
		end

		length += 1
		compatible_archetypes[length] = archetype
		indices[length] = records
	end

	return prepared_query(compatible_archetypes, components, indices)
end

type WorldIterator = (() -> (i53, { [unknown]: unknown? })) & (() -> ()) & (() -> i53)
-- __nominal_type_dont_use could not be any or T as it causes a type error
-- or produces a union
export type Entity<T = any> = number & { __nominal_type_dont_use: T }
export type Pair = number

export type QueryShim<T...> = typeof(setmetatable({
	without = function(...): QueryShim<T...>
		return nil :: any
	end,
}, {
	__iter = function(): () -> (number, T...)
		return nil :: any
	end,
}))

export type WorldShim = typeof(setmetatable(
	{} :: {

		--- Creates a new entity
		entity: (WorldShim) -> Entity,
		--- Creates a new entity located in the first 256 ids.
		--- These should be used for static components for fast access.
		component: <T>(WorldShim) -> Entity<T>,
		--- Gets the target of an relationship. For example, when a user calls
		--- `world:target(id, ChildOf(parent))`, you will obtain the parent entity.
		target: (WorldShim, id: Entity, relation: Entity) -> Entity?,
		--- Deletes an entity and all it's related components and relationships.
		delete: (WorldShim, id: Entity) -> (),

		--- Adds a component to the entity with no value
		add: <T>(WorldShim, id: Entity, component: Entity<T>) -> (),
		--- Assigns a value to a component on the given entity
		set: <T>(WorldShim, id: Entity, component: Entity<T>, data: T) -> (),
		--- Removes a component from the given entity
		remove: (WorldShim, id: Entity, component: Entity) -> (),
		--- Retrieves the value of up to 4 components. These values may be nil.
		get: (<A>(WorldShim, id: any, Entity<A>) -> A)
			& (<A, B>(WorldShim, id: Entity, Entity<A>, Entity<B>) -> (A, B))
			& (<A, B, C>(WorldShim, id: Entity, Entity<A>, Entity<B>, Entity<C>) -> (A, B, C))
			& <A, B, C, D>(WorldShim, id: Entity, Entity<A>, Entity<B>, Entity<C>, Entity<D>) -> (A, B, C, D),

		--- Searches the world for entities that match a given query
		query: (<A>(WorldShim, Entity<A>) -> QueryShim<A>)
			& (<A, B>(WorldShim, Entity<A>, Entity<B>) -> QueryShim<A, B>)
			& (<A, B, C>(WorldShim, Entity<A>, Entity<B>, Entity<C>) -> QueryShim<A, B, C>)
			& (<A, B, C, D>(WorldShim, Entity<A>, Entity<B>, Entity<C>, Entity<D>) -> QueryShim<A, B, C, D>)
			& (<A, B, C, D, E>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>
			) -> QueryShim<A, B, C, D, E>)
			& (<A, B, C, D, E, F>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>
			) -> QueryShim<A, B, C, D, E, F>)
			& (<A, B, C, D, E, F, G>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>,
				Entity<G>
			) -> QueryShim<A, B, C, D, E, F, G>)
			& (<A, B, C, D, E, F, G, H>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>,
				Entity<G>,
				Entity<H>
			) -> QueryShim<A, B, C, D, E, F, G, H>)
			& (<A, B, C, D, E, F, G, H, I>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>,
				Entity<G>,
				Entity<H>,
				Entity<I>
			) -> QueryShim<A, B, C, D, E, F, G, H, I>)
			& (<A, B, C, D, E, F, G, H, I, J>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>,
				Entity<G>,
				Entity<H>,
				Entity<I>,
				Entity<J>
			) -> QueryShim<A, B, C, D, E, F, G, H, I, J>)
			& (<A, B, C, D, E, F, G, H, I, J, K>(
				WorldShim,
				Entity<A>,
				Entity<B>,
				Entity<C>,
				Entity<D>,
				Entity<E>,
				Entity<F>,
				Entity<G>,
				Entity<H>,
				Entity<I>,
				Entity<J>,
				Entity<K>,
				...Entity<any>
			) -> QueryShim<A, B, C, D, E, F, G, H, I, J, K>),
	},
	{} :: {
		__iter: (world: WorldShim) -> () -> (number, { [unknown]: unknown? }),
	}
))

local World = {}
World.__index = World

function World.new()
	local self = setmetatable({
		archetype_index = {} :: { [string]: Archetype },
		archetypes = {} :: Archetypes,
		id_index = {} :: ComponentIndex,
		entity_index = {
			dense = {} :: { [i24]: i53 },
			sparse = {} :: { [i53]: Record },
		} :: EntityIndex,
		hooks = {
			[EcsOnAdd] = {},
		},
		next_archetype_id = 0,
		next_id = 0,
		next_entity_id = 0,
		root_archetype = (nil :: any) :: Archetype,
	}, World)
	self.root_archetype = archetype_of(self, {})

	-- Initialize built-in components
	next_entity_id(self.entity_index, EcsChildOf)

	return self
end

World.entity = entity
World.query = query
World.remove = remove
World.clear = clear
World.delete = delete
World.component = new_component
World.add = add
World.set = set
World.get = get
World.target = target
World.parent = parent

return {
	World = World :: { new: () -> WorldShim },

	OnAdd = EcsOnAdd :: Entity,
	OnRemove = EcsOnRemove :: Entity,
	OnSet = EcsOnSet :: Entity,

	Wildcard = EcsWildcard :: Entity,
	w = EcsWildcard :: Entity,
	ChildOf = EcsChildOf,
	Component = EcsComponent,

	Rest = EcsRest,

	IS_PAIR = ECS_IS_PAIR,
	ECS_ID = ECS_ENTITY_T_LO,
	ECS_PAIR = ECS_PAIR,
	ECS_GENERATION_INC = ECS_GENERATION_INC,
	ECS_GENERATION = ECS_GENERATION,
	ECS_PAIR_RELATION = ECS_PAIR_RELATION,
	ECS_PAIR_OBJECT = ECS_PAIR_OBJECT,

	pair = (ECS_PAIR :: any) :: <R, T>(pred: Entity, obj: Entity) -> number,
	getAlive = getAlive,
}
