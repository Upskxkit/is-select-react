interface BaseSelect {
  type: string,
  placeholder: string,
  className?: String,
  hasError?: boolean
}

export interface Item {
  value: any,
  label: string,
  checked?: boolean,
  disabled?: boolean,
  indeterminate?: boolean,
  id?: any
}

export interface BaseMenu<T> {
  cancelHandler: () => void,
  applyHandler: (data: T) => void,
  items: Item[],
  open: boolean
}

export interface SingleMenu extends BaseMenu<Item> {
}

export interface MultipleMenu extends BaseMenu<Item[]> {
}

export interface SelectButtonInput extends BaseSelect {
  handleClick: Function,
  pending?: boolean,
  opened: boolean,
  value: any
}

export interface SelectWrapper extends BaseSelect {
  multi?: boolean,
  onSelect: Function,
  list?: any[],
  value?: Item | Item[] | undefined,
  defaultValue?: Item | Item[] | undefined,
  request?: Function,
  iconUrl?: string
}

export interface WithPopper {
  children: any,
  relative: boolean,
  request?: Function
}
